{-# LANGUAGE CPP, TypeFamilies #-}

-- -----------------------------------------------------------------------------
-- | This is the top-level module in the LLVM code generator.
--
module LlvmCodeGen ( llvmCodeGen, llvmFixupAsm ) where

#include "HsVersions.h"

import Llvm
import LlvmCodeGen.Base
import LlvmCodeGen.CodeGen
import LlvmCodeGen.Data
import LlvmCodeGen.Ppr
import LlvmCodeGen.Regs
import LlvmMangler

import BlockId
import CgUtils ( fixStgRegisters )
import Cmm
import CmmUtils
import Hoopl.Block
import Hoopl.Label
import Hoopl.Collections
import Module
import Debug ( DebugBlock, debugToMap, cmmDebugGen )
import PprCmm

import BufWrite
import DynFlags
import ErrUtils
import FastString
import Outputable
import UniqSupply
import SysTools ( figureLlvmVersion )
import qualified Stream

import Control.Monad ( when )
import Data.Maybe ( fromMaybe, catMaybes )
import System.IO

-- -----------------------------------------------------------------------------
-- | Top-level of the LLVM Code generator
--
llvmCodeGen :: DynFlags -> ModLocation -> Handle -> UniqSupply
               -> Stream.Stream IO RawCmmGroup ()
               -> IO ()
llvmCodeGen dflags location h us cmm_stream
  = withTiming (pure dflags) (text "LLVM CodeGen") (const ()) $ do
       bufh <- newBufHandle h

       -- Pass header
       showPass dflags "LLVM CodeGen"

       -- get llvm version, cache for later use
       ver <- (fromMaybe supportedLlvmVersion) `fmap` figureLlvmVersion dflags

       -- warn if unsupported
       debugTraceMsg dflags 2
            (text "Using LLVM version:" <+> text (show ver))
       let doWarn = wopt Opt_WarnUnsupportedLlvmVersion dflags
       when (ver /= supportedLlvmVersion && doWarn) $
           putMsg dflags (text "You are using an unsupported version of LLVM!"
                            $+$ text ("Currently only " ++
                                      llvmVersionStr supportedLlvmVersion ++
                                      " is supported.")
                            $+$ text "We will try though...")

       -- run code generation
       runLlvm dflags ver bufh us $
         llvmCodeGen' location (liftStream cmm_stream)

       bFlush bufh

llvmCodeGen' :: ModLocation -> Stream.Stream LlvmM RawCmmGroup () -> LlvmM ()
llvmCodeGen' location cmm_stream
  = do  -- Preamble
        renderLlvm header
        ghcInternalFunctions
        cmmMetaLlvmPrelude

        -- Procedures
        let llvmStream = Stream.mapM (llvmGroupLlvmGens location) cmm_stream
        _ <- Stream.collect llvmStream

        -- Declare aliases for forward references
        renderLlvm . pprLlvmData =<< generateExternDecls

        -- Postamble
        cmmUsedLlvmGens

        -- Debug metadata
        debugInfoGen location
  where
    header :: SDoc
    header = sdocWithDynFlags $ \dflags ->
      let target = LLVM_TARGET
          layout = case lookup target (llvmTargets dflags) of
            Just (LlvmTarget dl _ _) -> dl
            Nothing -> error $ "Failed to lookup the datalayout for " ++ target ++ "; available targets: " ++ show (map fst $ llvmTargets dflags)
      in     text ("target datalayout = \"" ++ layout ++ "\"")
         $+$ text ("target triple = \"" ++ target ++ "\"")


debugInfoGen :: ModLocation -> LlvmM ()
debugInfoGen location
  = do  dflags <- getDynFlags
        fileMeta <- getMetaUniqueId
        subprogramsMeta <- getMetaUniqueId
        cuMeta <- getMetaUniqueId
        dwarfVersionMeta <- getMetaUniqueId
        debugInfoVersionMeta <- getMetaUniqueId
        getMetaDecls >>= renderLlvm . ppLlvmMetas
        subprograms <- getSubprograms
        renderLlvm $ ppLlvmMetas
            [ MetaUnnamed fileMeta $ MetaDIFile
              { difFilename     = fsLit $ fromMaybe "TODO" (ml_hs_file location)
              , difDirectory    = fsLit ""
              }
            , MetaUnnamed cuMeta $ MetaDICompileUnit
              { dicuLanguage    = fsLit "DW_LANG_Haskell"
              , dicuFile        = fileMeta
              , dicuProducer    = fsLit "ghc"
              , dicuIsOptimized = optLevel dflags > 0
              , dicuSubprograms = MetaStruct $ map MetaNode subprograms
              }
            , MetaNamed (fsLit "llvm.dbg.cu") [ cuMeta ]
            , MetaUnnamed subprogramsMeta $ MetaStruct []
            , MetaNamed (fsLit "llvm.module.flags")
              [ dwarfVersionMeta
              , debugInfoVersionMeta
              ]
            , MetaUnnamed dwarfVersionMeta $ MetaStruct
              [ MetaVar $ LMLitVar $ LMIntLit 2 i32
              , MetaStr $ fsLit "Dwarf Version"
              , MetaVar $ LMLitVar $ LMIntLit 4 i32
              ]
            , MetaUnnamed debugInfoVersionMeta $ MetaStruct
              [ MetaVar $ LMLitVar $ LMIntLit 2 i32
              , MetaStr $ fsLit "Debug Info Version"
              , MetaVar $ LMLitVar $ LMIntLit 3 i32
              ]
            ]


llvmGroupLlvmGens :: ModLocation -> RawCmmGroup -> LlvmM ()
llvmGroupLlvmGens location cmm = do

        dbg_lvl <- debugLevel <$> getDynFlags
        let debug_map :: LabelMap DebugBlock
            debug_map
              | dbg_lvl >= 1 = debugToMap $ cmmDebugGen location cmm
              | otherwise    = mapEmpty

        -- Insert functions into map, collect data
        let split (CmmData s d' )     = return $ Just (s, d')
            split (CmmProc h l live g) = do
              -- Set function type
              let l' = case mapLookup (g_entry g) h of
                         Nothing                   -> l
                         Just (Statics info_lbl _) -> info_lbl
              lml <- strCLabel_llvm l'
              funInsert lml =<< llvmFunTy live
              return Nothing
        cdata <- fmap catMaybes $ mapM split cmm

        {-# SCC "llvm_datas_gen" #-}
          cmmDataLlvmGens cdata
        {-# SCC "llvm_procs_gen" #-}
          mapM_ (cmmLlvmGen debug_map) cmm

-- -----------------------------------------------------------------------------
-- | Do LLVM code generation on all these Cmms data sections.
--
cmmDataLlvmGens :: [(Section,CmmStatics)] -> LlvmM ()

cmmDataLlvmGens statics
  = do lmdatas <- mapM genLlvmData statics

       let (gss, tss) = unzip lmdatas

       let regGlobal (LMGlobal (LMGlobalVar l ty _ _ _ _) _)
                        = funInsert l ty
           regGlobal _  = return ()
       mapM_ regGlobal (concat gss)
       gss' <- mapM aliasify $ concat gss

       renderLlvm $ pprLlvmData (concat gss', concat tss)

-- | LLVM can't handle entry blocks which loop back to themselves (could be
-- seen as an LLVM bug) so we rearrange the code to keep the original entry
-- label which branches to a newly generated second label that branches back
-- to itself. See: Trac #11649
fixBottom :: RawCmmDecl -> LlvmM RawCmmDecl
fixBottom cp@(CmmProc hdr entry_lbl live g) =
    maybe (pure cp) fix_block $ mapLookup (g_entry g) blk_map
  where
    blk_map = toBlockMap g

    fix_block :: CmmBlock -> LlvmM RawCmmDecl
    fix_block blk
        | (CmmEntry e_lbl tickscp, middle, CmmBranch b_lbl) <- blockSplit blk
        , isEmptyBlock middle
        , e_lbl == b_lbl = do
            new_lbl <- mkBlockId <$> getUniqueM

            let fst_blk =
                    BlockCC (CmmEntry e_lbl tickscp) BNil (CmmBranch new_lbl)
                snd_blk =
                    BlockCC (CmmEntry new_lbl tickscp) BNil (CmmBranch new_lbl)

            pure . CmmProc hdr entry_lbl live . ofBlockMap (g_entry g)
                $ mapFromList [(e_lbl, fst_blk), (new_lbl, snd_blk)]

    fix_block _ = pure cp

fixBottom rcd = pure rcd

-- | Complete LLVM code generation phase for a single top-level chunk of Cmm.
cmmLlvmGen :: LabelMap DebugBlock -> RawCmmDecl -> LlvmM ()
cmmLlvmGen debug_map cmm@CmmProc{} = do

    -- rewrite assignments to global regs
    dflags <- getDynFlag id
    fixed_cmm <- fixBottom $
                    {-# SCC "llvm_fix_regs" #-}
                    fixStgRegisters dflags cmm

    dumpIfSetLlvm Opt_D_dump_opt_cmm "Optimised Cmm" (pprCmmGroup [fixed_cmm])

    -- generate llvm code from cmm
    llvmBC <- withClearVars $ genLlvmProc fixed_cmm

    -- pretty print
    (docs, ivars) <- fmap unzip $ mapM (pprLlvmCmmDecl debug_map) llvmBC

    -- Output, note down used variables
    renderLlvm (vcat docs)
    mapM_ markUsedVar $ concat ivars

cmmLlvmGen _ _ = return ()

-- -----------------------------------------------------------------------------
-- | Generate meta data nodes
--

cmmMetaLlvmPrelude :: LlvmM ()
cmmMetaLlvmPrelude = do
  metas <- flip mapM stgTBAA $ \(uniq, name, parent) -> do
    -- Generate / lookup meta data IDs
    tbaaId <- getMetaUniqueId
    setUniqMeta uniq tbaaId
    parentId <- maybe (return Nothing) getUniqMeta parent
    -- Build definition
    return $ MetaUnnamed tbaaId $ MetaStruct $
          case parentId of
              Just p  -> [ MetaStr name, MetaNode p ]
              -- As of LLVM 4.0, a node without parents should be rendered as
              -- just a name on its own. Previously `null` was accepted as the
              -- name.
              Nothing -> [ MetaStr name ]
  renderLlvm $ ppLlvmMetas metas

-- -----------------------------------------------------------------------------
-- | Marks variables as used where necessary
--

cmmUsedLlvmGens :: LlvmM ()
cmmUsedLlvmGens = do

  -- LLVM would discard variables that are internal and not obviously
  -- used if we didn't provide these hints. This will generate a
  -- definition of the form
  --
  --   @llvm.used = appending global [42 x i8*] [i8* bitcast <var> to i8*, ...]
  --
  -- Which is the LLVM way of protecting them against getting removed.
  ivars <- getUsedVars
  let cast x = LMBitc (LMStaticPointer (pVarLift x)) i8Ptr
      ty     = (LMArray (length ivars) i8Ptr)
      usedArray = LMStaticArray (map cast ivars) ty
      sectName  = Just $ fsLit "llvm.metadata"
      lmUsedVar = LMGlobalVar (fsLit "llvm.used") ty Appending sectName Nothing Constant
      lmUsed    = LMGlobal lmUsedVar (Just usedArray)
  if null ivars
     then return ()
     else renderLlvm $ pprLlvmData ([lmUsed], [])
