{-
(c) The University of Glasgow 2006
(c) The GRASP/AQUA Project, Glasgow University, 1992-1998


The @Inst@ type: dictionaries or method instances
-}

{-# LANGUAGE CPP, MultiWayIf, TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}

module Inst (
       deeplySkolemise,
       topInstantiate, topInstantiateInferred, deeplyInstantiate,
       instCall, instDFunType, instStupidTheta, instTyVarsWith,
       newWanted, newWanteds,

       tcInstTyBinders, tcInstTyBinder,

       newOverloadedLit, mkOverLit,

       ClsInstMorph(..),

       newClsInst,
       tcGetInsts, tcGetInstEnvs, getOverlapFlag,
       tcExtendLocalInstEnv,
       tcExtendMorphs,
       instCallConstraints, newMethodFromName,
       tcSyntaxName,

       -- Simple functions over evidence variables
       tyCoVarsOfWC,
       tyCoVarsOfCt, tyCoVarsOfCts,
       expandTheta, expandSig, cover,

    ) where

#include "HsVersions.h"

import GhcPrelude

import {-# SOURCE #-}   TcExpr( tcPolyExpr, tcSyntaxOp )
import {-# SOURCE #-}   TcUnify( unifyType, unifyKind )

import BasicTypes ( IntegralLit(..), SourceText(..) )
import FastString
import HsSyn
import TcHsSyn
import TcRnMonad
import TcEnv
import TcEvidence
import InstEnv
import TysWiredIn  ( heqDataCon, eqDataCon )
import CoreSyn     ( isOrphan )
import FunDeps
import TcMType
import Type
import TyCoRep
import TcType
import HscTypes
import Class( Class )
import MkId( mkDictFunId )
import CoreSyn( Expr(..) )  -- For the Coercion constructor
import Id
import Name
import Var      ( EvVar, mkTyVar, tyVarName, VarBndr(..), varType, updateVarType )
import DataCon
import VarEnv
import PrelNames
import SrcLoc
import DynFlags
import Util
import Outputable
import Unify
import Control.Monad
import Class
import Data.List ( partition )
import Data.Maybe ( catMaybes )
import qualified GHC.LanguageExtensions as LangExt

import Control.Monad( unless )

{-
************************************************************************
*                                                                      *
                Creating and emittind constraints
*                                                                      *
************************************************************************
-}

newMethodFromName :: CtOrigin -> Name -> TcRhoType -> TcM (HsExpr GhcTcId)
-- Used when Name is the wired-in name for a wired-in class method,
-- so the caller knows its type for sure, which should be of form
--    forall a. C a => <blah>
-- newMethodFromName is supposed to instantiate just the outer
-- type variable and constraint

newMethodFromName origin name inst_ty
  = do { id <- tcLookupId name
              -- Use tcLookupId not tcLookupGlobalId; the method is almost
              -- always a class op, but with -XRebindableSyntax GHC is
              -- meant to find whatever thing is in scope, and that may
              -- be an ordinary function.

       ; let ty = piResultTy (idType id) inst_ty
             (theta, _caller_knows_this) = tcSplitPhiTy ty
       ; wrap <- ASSERT( not (isForAllTy ty) && isSingleton theta )
                 instCall origin [inst_ty] theta

       ; return (mkHsWrap wrap (HsVar noExt (noLoc id))) }

{-
************************************************************************
*                                                                      *
        Deep instantiation and skolemisation
*                                                                      *
************************************************************************

Note [Deep skolemisation]
~~~~~~~~~~~~~~~~~~~~~~~~~
deeplySkolemise decomposes and skolemises a type, returning a type
with all its arrows visible (ie not buried under foralls)

Examples:

  deeplySkolemise (Int -> forall a. Ord a => blah)
    =  ( wp, [a], [d:Ord a], Int -> blah )
    where wp = \x:Int. /\a. \(d:Ord a). <hole> x

  deeplySkolemise  (forall a. Ord a => Maybe a -> forall b. Eq b => blah)
    =  ( wp, [a,b], [d1:Ord a,d2:Eq b], Maybe a -> blah )
    where wp = /\a.\(d1:Ord a).\(x:Maybe a)./\b.\(d2:Ord b). <hole> x

In general,
  if      deeplySkolemise ty = (wrap, tvs, evs, rho)
    and   e :: rho
  then    wrap e :: ty
    and   'wrap' binds tvs, evs

ToDo: this eta-abstraction plays fast and loose with termination,
      because it can introduce extra lambdas.  Maybe add a `seq` to
      fix this
-}

deeplySkolemise :: TcSigmaType
                -> TcM ( HsWrapper
                       , [(Name,TyVar)]     -- All skolemised variables
                       , [EvVar]            -- All "given"s
                       , TcRhoType )

deeplySkolemise ty
  = go init_subst ty
  where
    init_subst = mkEmptyTCvSubst (mkInScopeSet (tyCoVarsOfType ty))

    go subst ty
      | Just (arg_tys, tvs, theta, ty') <- tcDeepSplitSigmaTy_maybe ty
      = do { let arg_tys' = substTys subst arg_tys
           ; ids1           <- newSysLocalIds (fsLit "dk") arg_tys'
           ; (subst', tvs1) <- tcInstSkolTyVarsX subst tvs
           ; ev_vars1       <- newEvVars (substTheta subst' theta)
           ; (wrap, tvs_prs2, ev_vars2, rho) <- go subst' ty'
           ; let tv_prs1 = map tyVarName tvs `zip` tvs1
           ; return ( mkWpLams ids1
                      <.> mkWpTyLams tvs1
                      <.> mkWpLams ev_vars1
                      <.> wrap
                      <.> mkWpEvVarApps ids1
                    , tv_prs1  ++ tvs_prs2
                    , ev_vars1 ++ ev_vars2
                    , mkFunTys arg_tys' rho ) }

      | otherwise
      = return (idHsWrapper, [], [], substTy subst ty)
        -- substTy is a quick no-op on an empty substitution

-- | Instantiate all outer type variables
-- and any context. Never looks through arrows.
topInstantiate :: CtOrigin -> TcSigmaType -> TcM (HsWrapper, TcRhoType)
-- if    topInstantiate ty = (wrap, rho)
-- and   e :: ty
-- then  wrap e :: rho  (that is, wrap :: ty "->" rho)
topInstantiate = top_instantiate True

-- | Instantiate all outer 'Inferred' binders
-- and any context. Never looks through arrows or specified type variables.
-- Used for visible type application.
topInstantiateInferred :: CtOrigin -> TcSigmaType
                       -> TcM (HsWrapper, TcSigmaType)
-- if    topInstantiate ty = (wrap, rho)
-- and   e :: ty
-- then  wrap e :: rho
topInstantiateInferred = top_instantiate False

top_instantiate :: Bool   -- True  <=> instantiate *all* variables
                          -- False <=> instantiate only the inferred ones
                -> CtOrigin -> TcSigmaType -> TcM (HsWrapper, TcRhoType)
top_instantiate inst_all orig ty
  | not (null binders && null theta)
  = do { let (inst_bndrs, leave_bndrs) = span should_inst binders
             (inst_theta, leave_theta)
               | null leave_bndrs = (theta, [])
               | otherwise        = ([], theta)
             in_scope    = mkInScopeSet (tyCoVarsOfType ty)
             empty_subst = mkEmptyTCvSubst in_scope
             inst_tvs    = binderVars inst_bndrs
       ; (subst, inst_tvs') <- mapAccumLM newMetaTyVarX empty_subst inst_tvs
       ; let inst_theta' = substTheta subst inst_theta
             sigma'      = substTy subst (mkForAllTys leave_bndrs $
                                          mkFunTys leave_theta rho)
             inst_tv_tys' = mkTyVarTys inst_tvs'

       ; wrap1 <- instCall orig inst_tv_tys' inst_theta'
       ; traceTc "Instantiating"
                 (vcat [ text "all tyvars?" <+> ppr inst_all
                       , text "origin" <+> pprCtOrigin orig
                       , text "type" <+> debugPprType ty
                       , text "theta" <+> ppr theta
                       , text "leave_bndrs" <+> ppr leave_bndrs
                       , text "with" <+> vcat (map debugPprType inst_tv_tys')
                       , text "theta:" <+>  ppr inst_theta' ])

       ; (wrap2, rho2) <-
           if null leave_bndrs

         -- account for types like forall a. Num a => forall b. Ord b => ...
           then top_instantiate inst_all orig sigma'

         -- but don't loop if there were any un-inst'able tyvars
           else return (idHsWrapper, sigma')

       ; return (wrap2 <.> wrap1, rho2) }

  | otherwise = return (idHsWrapper, ty)
  where
    (binders, phi) = tcSplitForAllVarBndrs ty
    (theta, rho)   = tcSplitPhiTy phi

    should_inst bndr
      | inst_all  = True
      | otherwise = binderArgFlag bndr == Inferred

deeplyInstantiate :: CtOrigin -> TcSigmaType -> TcM (HsWrapper, TcRhoType)
--   Int -> forall a. a -> a  ==>  (\x:Int. [] x alpha) :: Int -> alpha
-- In general if
-- if    deeplyInstantiate ty = (wrap, rho)
-- and   e :: ty
-- then  wrap e :: rho
-- That is, wrap :: ty ~> rho
--
-- If you don't need the HsWrapper returned from this function, consider
-- using tcSplitNestedSigmaTys in TcType, which is a pure alternative that
-- only computes the returned TcRhoType.

deeplyInstantiate orig ty =
  deeply_instantiate orig
                     (mkEmptyTCvSubst (mkInScopeSet (tyCoVarsOfType ty)))
                     ty

deeply_instantiate :: CtOrigin
                   -> TCvSubst
                   -> TcSigmaType -> TcM (HsWrapper, TcRhoType)
-- Internal function to deeply instantiate that builds on an existing subst.
-- It extends the input substitution and applies the final subtitution to
-- the types on return.  See #12549.

deeply_instantiate orig subst ty
  | Just (arg_tys, tvs, theta, rho) <- tcDeepSplitSigmaTy_maybe ty
  = do { (subst', tvs') <- newMetaTyVarsX subst tvs
       ; let arg_tys' = substTys   subst' arg_tys
             theta'   = substTheta subst' theta
       ; ids1  <- newSysLocalIds (fsLit "di") arg_tys'
       ; wrap1 <- instCall orig (mkTyVarTys tvs') theta'
       ; traceTc "Instantiating (deeply)" (vcat [ text "origin" <+> pprCtOrigin orig
                                                , text "type" <+> ppr ty
                                                , text "with" <+> ppr tvs'
                                                , text "args:" <+> ppr ids1
                                                , text "theta:" <+>  ppr theta'
                                                , text "subst:" <+> ppr subst'])
       ; (wrap2, rho2) <- deeply_instantiate orig subst' rho
       ; return (mkWpLams ids1
                    <.> wrap2
                    <.> wrap1
                    <.> mkWpEvVarApps ids1,
                 mkFunTys arg_tys' rho2) }

  | otherwise
  = do { let ty' = substTy subst ty
       ; traceTc "deeply_instantiate final subst"
                 (vcat [ text "origin:"   <+> pprCtOrigin orig
                       , text "type:"     <+> ppr ty
                       , text "new type:" <+> ppr ty'
                       , text "subst:"    <+> ppr subst ])
      ; return (idHsWrapper, ty') }


instTyVarsWith :: CtOrigin -> [TyVar] -> [TcType] -> TcM TCvSubst
-- Use this when you want to instantiate (forall a b c. ty) with
-- types [ta, tb, tc], but when the kinds of 'a' and 'ta' might
-- not yet match (perhaps because there are unsolved constraints; Trac #14154)
-- If they don't match, emit a kind-equality to promise that they will
-- eventually do so, and thus make a kind-homongeneous substitution.
instTyVarsWith orig tvs tys
  = go empty_subst tvs tys
  where
    empty_subst = mkEmptyTCvSubst (mkInScopeSet (tyCoVarsOfTypes tys))

    go subst [] []
      = return subst
    go subst (tv:tvs) (ty:tys)
      | tv_kind `tcEqType` ty_kind
      = go (extendTCvSubst subst tv ty) tvs tys
      | otherwise
      = do { co <- emitWantedEq orig KindLevel Nominal ty_kind tv_kind
           ; go (extendTCvSubst subst tv (ty `mkCastTy` co)) tvs tys }
      where
        tv_kind = substTy subst (tyVarKind tv)
        ty_kind = tcTypeKind ty

    go _ _ _ = pprPanic "instTysWith" (ppr tvs $$ ppr tys)

{-
************************************************************************
*                                                                      *
            Instantiating a call
*                                                                      *
************************************************************************

Note [Handling boxed equality]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
The solver deals entirely in terms of unboxed (primitive) equality.
There should never be a boxed Wanted equality. Ever. But, what if
we are calling `foo :: forall a. (F a ~ Bool) => ...`? That equality
is boxed, so naive treatment here would emit a boxed Wanted equality.

So we simply check for this case and make the right boxing of evidence.

-}

----------------
instCall :: CtOrigin -> [TcType] -> TcThetaType -> TcM HsWrapper
-- Instantiate the constraints of a call
--      (instCall o tys theta)
-- (a) Makes fresh dictionaries as necessary for the constraints (theta)
-- (b) Throws these dictionaries into the LIE
-- (c) Returns an HsWrapper ([.] tys dicts)

instCall orig tys theta
  = do  { dict_app <- instCallConstraints orig theta
        ; return (dict_app <.> mkWpTyApps tys) }

----------------
instCallConstraints :: CtOrigin -> TcThetaType -> TcM HsWrapper
-- Instantiates the TcTheta, puts all constraints thereby generated
-- into the LIE, and returns a HsWrapper to enclose the call site.

instCallConstraints orig preds
  | null preds
  = return idHsWrapper
  | otherwise
  = do { evs <- mapM go preds
       ; traceTc "instCallConstraints" (ppr evs)
       ; return (mkWpEvApps evs) }
  where
    go :: TcPredType -> TcM EvTerm
    go pred
     | Just (Nominal, ty1, ty2) <- getEqPredTys_maybe pred -- Try short-cut #1
     = do  { co <- unifyType Nothing ty1 ty2
           ; return (evCoercion co) }

       -- Try short-cut #2
     | Just (tc, args@[_, _, ty1, ty2]) <- splitTyConApp_maybe pred
     , tc `hasKey` heqTyConKey
     = do { co <- unifyType Nothing ty1 ty2
          ; return (evDFunApp (dataConWrapId heqDataCon) args [Coercion co]) }

     | otherwise
     = emitWanted orig pred

instDFunType :: DFunId -> [DFunInstType]
             -> TcM ( [TcType]      -- instantiated argument types
                    , TcThetaType ) -- instantiated constraint
-- See Note [DFunInstType: instantiating types] in InstEnv
instDFunType dfun_id dfun_inst_tys
  = do { (subst, inst_tys) <- go empty_subst dfun_tvs dfun_inst_tys
       ; return (inst_tys, substTheta subst dfun_theta) }
  where
    dfun_ty = idType dfun_id
    (dfun_tvs, dfun_theta, _) = tcSplitSigmaTy dfun_ty
    empty_subst = mkEmptyTCvSubst (mkInScopeSet (tyCoVarsOfType dfun_ty))
                  -- With quantified constraints, the
                  -- type of a dfun may not be closed

    go :: TCvSubst -> [TyVar] -> [DFunInstType] -> TcM (TCvSubst, [TcType])
    go subst [] [] = return (subst, [])
    go subst (tv:tvs) (Just ty : mb_tys)
      = do { (subst', tys) <- go (extendTvSubstAndInScope subst tv ty)
                                 tvs
                                 mb_tys
           ; return (subst', ty : tys) }
    go subst (tv:tvs) (Nothing : mb_tys)
      = do { (subst', tv') <- newMetaTyVarX subst tv
           ; (subst'', tys) <- go subst' tvs mb_tys
           ; return (subst'', mkTyVarTy tv' : tys) }
    go _ _ _ = pprPanic "instDFunTypes" (ppr dfun_id $$ ppr dfun_inst_tys)

----------------
instStupidTheta :: CtOrigin -> TcThetaType -> TcM ()
-- Similar to instCall, but only emit the constraints in the LIE
-- Used exclusively for the 'stupid theta' of a data constructor
instStupidTheta orig theta
  = do  { _co <- instCallConstraints orig theta -- Discard the coercion
        ; return () }

{-
************************************************************************
*                                                                      *
         Instantiating Kinds
*                                                                      *
************************************************************************

Note [Constraints handled in types]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Generally, we cannot handle constraints written in types. For example,
if we declare

  data C a where
    MkC :: Show a => a -> C a

we will not be able to use MkC in types, as we have no way of creating
a type-level Show dictionary.

However, we make an exception for equality types. Consider

  data T1 a where
    MkT1 :: T1 Bool

  data T2 a where
    MkT2 :: a ~ Bool => T2 a

MkT1 has a constrained return type, while MkT2 uses an explicit equality
constraint. These two types are often written interchangeably, with a
reasonable expectation that they mean the same thing. For this to work --
and for us to be able to promote GADTs -- we need to be able to instantiate
equality constraints in types.

One wrinkle is that the equality in MkT2 is *lifted*. But, for proper
GADT equalities, GHC produces *unlifted* constraints. (This unlifting comes
from DataCon.eqSpecPreds, which uses mkPrimEqPred.) And, perhaps a wily
user will use (~~) for a heterogeneous equality. We thus must support
all of (~), (~~), and (~#) in types. (See Note [The equality types story]
in TysPrim for a primer on these equality types.)

The get_eq_tys_maybe function recognizes these three forms of equality,
returning a suitable type formation function and the two types related
by the equality constraint. In the lifted case, it uses mkHEqBoxTy or
mkEqBoxTy, which promote the datacons of the (~~) or (~) datatype,
respectively.

One might reasonably wonder who *unpacks* these boxes once they are
made. After all, there is no type-level `case` construct. The surprising
answer is that no one ever does. Instead, if a GADT constructor is used
on the left-hand side of a type family equation, that occurrence forces
GHC to unify the types in question. For example:

  data G a where
    MkG :: G Bool

  type family F (x :: G a) :: a where
    F MkG = False

When checking the LHS `F MkG`, GHC sees the MkG constructor and then must
unify F's implicit parameter `a` with Bool. This succeeds, making the equation

    F Bool (MkG @Bool <Bool>) = False

Note that we never need unpack the coercion. This is because type family
equations are *not* parametric in their kind variables. That is, we could have
just said

  type family H (x :: G a) :: a where
    H _ = False

The presence of False on the RHS also forces `a` to become Bool, giving us

    H Bool _ = False

The fact that any of this works stems from the lack of phase separation between
types and kinds (unlike the very present phase separation between terms and types).

Once we have the ability to pattern-match on types below top-level, this will
no longer cut it, but it seems fine for now.

-}

---------------------------
-- | Instantantiate the TyConBinders of a forall type,
--   given its decomposed form (tvs, ty)
tcInstTyBinders :: HasDebugCallStack
              => ([TyCoBinder], TcKind)   -- ^ The type (forall bs. ty)
              -> TcM ([TcType], TcKind)   -- ^ Instantiated bs, substituted ty
-- Takes a pair because that is what splitPiTysInvisible returns
-- See also Note [Bidirectional type checking]
tcInstTyBinders (bndrs, ty)
  | null bndrs        -- It's fine for bndrs to be empty e.g.
  = return ([], ty)   -- Check that (Maybe :: forall {k}. k->*),
                      --       and see the call to instTyBinders in checkExpectedKind
                      -- A user bug to be reported as such; it is not a compiler crash!

  | otherwise
  = do { (subst, args) <- mapAccumLM (tcInstTyBinder Nothing) empty_subst bndrs
       ; ty' <- zonkTcType (substTy subst ty)
                   -- Why zonk the result? So that tcTyVar can
                   -- obey (IT6) of Note [The tcType invariant] in TcHsType
                   -- ToDo: SLPJ: I don't think this is needed
       ; return (args, ty') }
  where
     empty_subst = mkEmptyTCvSubst (mkInScopeSet (tyCoVarsOfType ty))

-- | Used only in *types*
tcInstTyBinder :: Maybe (VarEnv Kind)
               -> TCvSubst -> TyBinder -> TcM (TCvSubst, TcType)
tcInstTyBinder mb_kind_info subst (Named (Bndr tv _))
  = case lookup_tv tv of
      Just ki -> return (extendTvSubstAndInScope subst tv ki, ki)
      Nothing -> do { (subst', tv') <- newMetaTyVarX subst tv
                    ; return (subst', mkTyVarTy tv') }
  where
    lookup_tv tv = do { env <- mb_kind_info   -- `Maybe` monad
                      ; lookupVarEnv env tv }


tcInstTyBinder _ subst (Anon ty)
     -- This is the *only* constraint currently handled in types.
  | Just (mk, k1, k2) <- get_eq_tys_maybe substed_ty
  = do { co <- unifyKind Nothing k1 k2
       ; arg' <- mk co
       ; return (subst, arg') }

  | isPredTy substed_ty
  = do { let (env, tidy_ty) = tidyOpenType emptyTidyEnv substed_ty
       ; addErrTcM (env, text "Illegal constraint in a kind:" <+> ppr tidy_ty)

         -- just invent a new variable so that we can continue
       ; u <- newUnique
       ; let name = mkSysTvName u (fsLit "dict")
       ; return (subst, mkTyVarTy $ mkTyVar name substed_ty) }


  | otherwise
  = do { tv_ty <- newFlexiTyVarTy substed_ty
       ; return (subst, tv_ty) }

  where
    substed_ty = substTy subst ty

      -- See Note [Constraints handled in types]
    get_eq_tys_maybe :: Type
                     -> Maybe ( Coercion -> TcM Type
                                 -- given a coercion proving t1 ~# t2, produce the
                                 -- right instantiation for the TyBinder at hand
                              , Type  -- t1
                              , Type  -- t2
                              )
    get_eq_tys_maybe ty
        -- unlifted equality (~#)
      | Just (Nominal, k1, k2) <- getEqPredTys_maybe ty
      = Just (\co -> return $ mkCoercionTy co, k1, k2)

        -- lifted heterogeneous equality (~~)
      | Just (tc, [_, _, k1, k2]) <- splitTyConApp_maybe ty
      = if | tc `hasKey` heqTyConKey
             -> Just (\co -> mkHEqBoxTy co k1 k2, k1, k2)
           | otherwise
             -> Nothing

        -- lifted homogeneous equality (~)
      | Just (tc, [_, k1, k2]) <- splitTyConApp_maybe ty
      = if | tc `hasKey` eqTyConKey
             -> Just (\co -> mkEqBoxTy co k1 k2, k1, k2)
           | otherwise
             -> Nothing

      | otherwise
      = Nothing

-------------------------------
-- | This takes @a ~# b@ and returns @a ~~ b@.
mkHEqBoxTy :: TcCoercion -> Type -> Type -> TcM Type
-- monadic just for convenience with mkEqBoxTy
mkHEqBoxTy co ty1 ty2
  = return $
    mkTyConApp (promoteDataCon heqDataCon) [k1, k2, ty1, ty2, mkCoercionTy co]
  where k1 = tcTypeKind ty1
        k2 = tcTypeKind ty2

-- | This takes @a ~# b@ and returns @a ~ b@.
mkEqBoxTy :: TcCoercion -> Type -> Type -> TcM Type
mkEqBoxTy co ty1 ty2
  = return $
    mkTyConApp (promoteDataCon eqDataCon) [k, ty1, ty2, mkCoercionTy co]
  where k = tcTypeKind ty1

{-
************************************************************************
*                                                                      *
                Literals
*                                                                      *
************************************************************************

-}

{-
In newOverloadedLit we convert directly to an Int or Integer if we
know that's what we want.  This may save some time, by not
temporarily generating overloaded literals, but it won't catch all
cases (the rest are caught in lookupInst).

-}

newOverloadedLit :: HsOverLit GhcRn
                 -> ExpRhoType
                 -> TcM (HsOverLit GhcTcId)
newOverloadedLit
  lit@(OverLit { ol_val = val, ol_ext = rebindable }) res_ty
  | not rebindable
    -- all built-in overloaded lits are tau-types, so we can just
    -- tauify the ExpType
  = do { res_ty <- expTypeToType res_ty
       ; dflags <- getDynFlags
       ; case shortCutLit dflags val res_ty of
        -- Do not generate a LitInst for rebindable syntax.
        -- Reason: If we do, tcSimplify will call lookupInst, which
        --         will call tcSyntaxName, which does unification,
        --         which tcSimplify doesn't like
           Just expr -> return (lit { ol_witness = expr
                                    , ol_ext = OverLitTc False res_ty })
           Nothing   -> newNonTrivialOverloadedLit orig lit
                                                   (mkCheckExpType res_ty) }

  | otherwise
  = newNonTrivialOverloadedLit orig lit res_ty
  where
    orig = LiteralOrigin lit
newOverloadedLit XOverLit{} _ = panic "newOverloadedLit"

-- Does not handle things that 'shortCutLit' can handle. See also
-- newOverloadedLit in TcUnify
newNonTrivialOverloadedLit :: CtOrigin
                           -> HsOverLit GhcRn
                           -> ExpRhoType
                           -> TcM (HsOverLit GhcTcId)
newNonTrivialOverloadedLit orig
  lit@(OverLit { ol_val = val, ol_witness = HsVar _ (L _ meth_name)
               , ol_ext = rebindable }) res_ty
  = do  { hs_lit <- mkOverLit val
        ; let lit_ty = hsLitType hs_lit
        ; (_, fi') <- tcSyntaxOp orig (mkRnSyntaxExpr meth_name)
                                      [synKnownType lit_ty] res_ty $
                      \_ -> return ()
        ; let L _ witness = nlHsSyntaxApps fi' [nlHsLit hs_lit]
        ; res_ty <- readExpType res_ty
        ; return (lit { ol_witness = witness
                      , ol_ext = OverLitTc rebindable res_ty }) }
newNonTrivialOverloadedLit _ lit _
  = pprPanic "newNonTrivialOverloadedLit" (ppr lit)

------------
mkOverLit ::OverLitVal -> TcM (HsLit GhcTc)
mkOverLit (HsIntegral i)
  = do  { integer_ty <- tcMetaTy integerTyConName
        ; return (HsInteger (il_text i)
                            (il_value i) integer_ty) }

mkOverLit (HsFractional r)
  = do  { rat_ty <- tcMetaTy rationalTyConName
        ; return (HsRat noExt r rat_ty) }

mkOverLit (HsIsString src s) = return (HsString src s)

{-
************************************************************************
*                                                                      *
                Re-mappable syntax

     Used only for arrow syntax -- find a way to nuke this
*                                                                      *
************************************************************************

Suppose we are doing the -XRebindableSyntax thing, and we encounter
a do-expression.  We have to find (>>) in the current environment, which is
done by the rename. Then we have to check that it has the same type as
Control.Monad.(>>).  Or, more precisely, a compatible type. One 'customer' had
this:

  (>>) :: HB m n mn => m a -> n b -> mn b

So the idea is to generate a local binding for (>>), thus:

        let then72 :: forall a b. m a -> m b -> m b
            then72 = ...something involving the user's (>>)...
        in
        ...the do-expression...

Now the do-expression can proceed using then72, which has exactly
the expected type.

In fact tcSyntaxName just generates the RHS for then72, because we only
want an actual binding in the do-expression case. For literals, we can
just use the expression inline.
-}

tcSyntaxName :: CtOrigin
             -> TcType                 -- ^ Type to instantiate it at
             -> (Name, HsExpr GhcRn)   -- ^ (Standard name, user name)
             -> TcM (Name, HsExpr GhcTcId)
                                       -- ^ (Standard name, suitable expression)
-- USED ONLY FOR CmdTop (sigh) ***
-- See Note [CmdSyntaxTable] in HsExpr

tcSyntaxName orig ty (std_nm, HsVar _ (L _ user_nm))
  | std_nm == user_nm
  = do rhs <- newMethodFromName orig std_nm ty
       return (std_nm, rhs)

tcSyntaxName orig ty (std_nm, user_nm_expr) = do
    std_id <- tcLookupId std_nm
    let
        -- C.f. newMethodAtLoc
        ([tv], _, tau) = tcSplitSigmaTy (idType std_id)
        sigma1         = substTyWith [tv] [ty] tau
        -- Actually, the "tau-type" might be a sigma-type in the
        -- case of locally-polymorphic methods.

    addErrCtxtM (syntaxNameCtxt user_nm_expr orig sigma1) $ do

        -- Check that the user-supplied thing has the
        -- same type as the standard one.
        -- Tiresome jiggling because tcCheckSigma takes a located expression
     span <- getSrcSpanM
     expr <- tcPolyExpr (L span user_nm_expr) sigma1
     return (std_nm, unLoc expr)

syntaxNameCtxt :: HsExpr GhcRn -> CtOrigin -> Type -> TidyEnv
               -> TcRn (TidyEnv, SDoc)
syntaxNameCtxt name orig ty tidy_env
  = do { inst_loc <- getCtLocM orig (Just TypeLevel)
       ; let msg = vcat [ text "When checking that" <+> quotes (ppr name)
                          <+> text "(needed by a syntactic construct)"
                        , nest 2 (text "has the required type:"
                                  <+> ppr (tidyType tidy_env ty))
                        , nest 2 (pprCtLoc inst_loc) ]
       ; return (tidy_env, msg) }

{-
************************************************************************
*                                                                      *
                Instances
*                                                                      *
************************************************************************
-}

getOverlapFlag :: Maybe OverlapMode -> TcM OverlapFlag
-- Construct the OverlapFlag from the global module flags,
-- but if the overlap_mode argument is (Just m),
--     set the OverlapMode to 'm'
getOverlapFlag overlap_mode
  = do  { dflags <- getDynFlags
        ; let overlap_ok    = xopt LangExt.OverlappingInstances dflags
              incoherent_ok = xopt LangExt.IncoherentInstances  dflags
              use x = OverlapFlag { isSafeOverlap = safeLanguageOn dflags
                                  , overlapMode   = x }
              default_oflag | incoherent_ok = use (Incoherent NoSourceText)
                            | overlap_ok    = use (Overlaps NoSourceText)
                            | otherwise     = use (NoOverlap NoSourceText)

              final_oflag = setOverlapModeMaybe default_oflag overlap_mode
        ; return final_oflag }

tcGetInsts :: TcM [ClsInst]
-- Gets the local class instances.
tcGetInsts = fmap tcg_insts getGblEnv

newClsInst :: Maybe OverlapMode -> Name -> [TyVar] -> ThetaType
           -> Class -> [Type] -> TcM ClsInst
newClsInst overlap_mode dfun_name tvs theta clas tys
  = do { (subst, tvs') <- freshenTyVarBndrs tvs
             -- Be sure to freshen those type variables,
             -- so they are sure not to appear in any lookup
       ; let tys' = substTys subst tys

             dfun = mkDictFunId dfun_name tvs theta clas tys
             -- The dfun uses the original 'tvs' because
             -- (a) they don't need to be fresh
             -- (b) they may be mentioned in the ib_binds field of
             --     an InstInfo, and in TcEnv.pprInstInfoDetails it's
             --     helpful to use the same names

       ; oflag <- getOverlapFlag overlap_mode
       ; let inst = mkLocalInstance dfun oflag tvs' clas tys'
       ; warnIfFlag Opt_WarnOrphans
                    (isOrphan (is_orphan inst))
                    (instOrphWarn inst)
       ; return inst }

instOrphWarn :: ClsInst -> SDoc
instOrphWarn inst
  = hang (text "Orphan instance:") 2 (pprInstanceHdr inst)
    $$ text "To avoid this"
    $$ nest 4 (vcat possibilities)
  where
    possibilities =
      text "move the instance declaration to the module of the class or of the type, or" :
      text "wrap the type with a newtype and declare the instance on the new type." :
      []

tcExtendMorphs :: [Morph] -> TcM a -> TcM a
tcExtendMorphs ms thing_inside = do
  traceTc "Adding morphisms:" (vcat (map ppr ms))
  env <- getGblEnv
  let env' = env { tcg_morphs_env = tcg_morphs_env env ++ ms
                 , tcg_morphs = tcg_morphs env ++ ms}
  setGblEnv env' thing_inside

tcExtendLocalInstEnv :: [ClsInst] -> TcM a -> TcM a
  -- Add new locally-defined instances
tcExtendLocalInstEnv dfuns thing_inside
 = do { traceDFuns dfuns
      ; env <- getGblEnv
      ; (inst_env', cls_insts') <- foldlM addLocalInst
                                          (tcg_inst_env env, tcg_insts env)
                                          dfuns
      ; let env' = env { tcg_insts    = cls_insts'
                       , tcg_inst_env = inst_env' }
      ; setGblEnv env' thing_inside }

addLocalInst :: (InstEnv, [ClsInst]) -> ClsInst -> TcM (InstEnv, [ClsInst])
-- Check that the proposed new instance is OK,
-- and then add it to the home inst env
-- If overwrite_inst, then we can overwrite a direct match
addLocalInst (home_ie, my_insts) ispec
   = do {
             -- Load imported instances, so that we report
             -- duplicates correctly

             -- 'matches'  are existing instance declarations that are less
             --            specific than the new one
             -- 'dups'     are those 'matches' that are equal to the new one
         ; isGHCi <- getIsGHCi
         ; eps    <- getEps
         ; tcg_env <- getGblEnv

           -- In GHCi, we *override* any identical instances
           -- that are also defined in the interactive context
           -- See Note [Override identical instances in GHCi]
         ; let home_ie'
                 | isGHCi    = deleteFromInstEnv home_ie ispec
                 | otherwise = home_ie

               global_ie = eps_inst_env eps
               inst_envs = InstEnvs { ie_global  = global_ie
                                    , ie_local   = home_ie'
                                    , ie_visible = tcVisibleOrphanMods tcg_env }

             -- Check for inconsistent functional dependencies
         ; let inconsistent_ispecs = checkFunDeps inst_envs ispec
         ; unless (null inconsistent_ispecs) $
           funDepErr ispec inconsistent_ispecs

             -- Check for duplicate instance decls.
         ; let (_tvs, cls, tys) = instanceHead ispec
               (matches, _, _)  = lookupInstEnv False inst_envs cls tys
               dups             = filter (identicalClsInstHead ispec) (map fst matches)
         ; unless (null dups) $
           dupInstErr ispec (head dups)

         ; return (extendInstEnv home_ie' ispec, ispec : my_insts) }

{-
Note [Signature files and type class instances]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Instances in signature files do not have an effect when compiling:
when you compile a signature against an implementation, you will
see the instances WHETHER OR NOT the instance is declared in
the file (this is because the signatures go in the EPS and we
can't filter them out easily.)  This is also why we cannot
place the instance in the hi file: it would show up as a duplicate,
and we don't have instance reexports anyway.

However, you might find them useful when typechecking against
a signature: the instance is a way of indicating to GHC that
some instance exists, in case downstream code uses it.

Implementing this is a little tricky.  Consider the following
situation (sigof03):

 module A where
     instance C T where ...

 module ASig where
     instance C T

When compiling ASig, A.hi is loaded, which brings its instances
into the EPS.  When we process the instance declaration in ASig,
we should ignore it for the purpose of doing a duplicate check,
since it's not actually a duplicate. But don't skip the check
entirely, we still want this to fail (tcfail221):

 module ASig where
     instance C T
     instance C T

Note that in some situations, the interface containing the type
class instances may not have been loaded yet at all.  The usual
situation when A imports another module which provides the
instances (sigof02m):

 module A(module B) where
     import B

See also Note [Signature lazy interface loading].  We can't
rely on this, however, since sometimes we'll have spurious
type class instances in the EPS, see #9422 (sigof02dm)

************************************************************************
*                                                                      *
        Errors and tracing
*                                                                      *
************************************************************************
-}

traceDFuns :: [ClsInst] -> TcRn ()
traceDFuns ispecs
  = traceTc "Adding instances:" (vcat (map pp ispecs))
  where
    pp ispec = hang (ppr (instanceDFunId ispec) <+> colon)
                  2 (ppr ispec)
        -- Print the dfun name itself too

funDepErr :: ClsInst -> [ClsInst] -> TcRn ()
funDepErr ispec ispecs
  = addClsInstsErr (text "Functional dependencies conflict between instance declarations:")
                    (ispec : ispecs)

dupInstErr :: ClsInst -> ClsInst -> TcRn ()
dupInstErr ispec dup_ispec
  = addClsInstsErr (text "Duplicate instance declarations:")
                    [ispec, dup_ispec]

addClsInstsErr :: SDoc -> [ClsInst] -> TcRn ()
addClsInstsErr herald ispecs
  = setSrcSpan (getSrcSpan (head sorted)) $
    addErr (hang herald 2 (pprInstances sorted))
 where
   sorted = sortWith getSrcLoc ispecs
   -- The sortWith just arranges that instances are dislayed in order
   -- of source location, which reduced wobbling in error messages,
   -- and is better for users

{-
************************************************************************
*                                                                      *
        Class Morphisms
*                                                                      *
************************************************************************
-}

---------------------------------------------
-- Here we store information that we'll need to make the
-- bindings for the generated instances
data ClsInstMorph
  = ClsInstMorph
      { info_cls   :: ClsInst -- Instance
      , info_morph :: Maybe Morph  -- ^ Generated with this morphisms
      , ant_dfun   :: Maybe DFunId -- DFunId of the antecedent of the morphism
      }

instance Outputable ClsInstMorph where
   ppr ci = text "ClsInstInfo: "
         <+> ppr (info_cls ci)
         <+> text "generated with morphism "
         <+> ppr (info_morph ci)

-- Auxiliary function
elemBy :: (a -> a -> Bool) -> [a] -> a -> Bool
elemBy eq xs x = any (eq x) xs

---------------------------------------------
-- These functions calculate the closure of a context using its superclasses,
-- its related morphisms or both.

-- TODO: factor them together.

expandThetaMO :: [Type] -> TcM [Type]
expandThetaMO tys =
  do res <- loop [] tys
     traceTc "expandThetaMO = " $ ppr res
     return res
  where
  loop ts [] = return ts
  loop ts frontier = do
    let all = ts ++ frontier
    ts' <- expandThetaMO_step frontier
    let new_frontier = filter ( not . (elemBy eqType all) ) ts'
    loop all new_frontier
---------------
expandThetaSC :: [Type] -> TcM [Type]
expandThetaSC tys =
  do res <- loop [] tys
     traceTc "expandThetaSC = " $ ppr res
     return res
  where
  loop ts [] = return ts
  loop ts frontier = do
    let all = ts ++ frontier
    ts' <- expandThetaSC_step frontier
    let new_frontier = filter ( not . (elemBy eqType all) ) ts'
    loop all new_frontier
---------------
expandTheta :: [Type] -> TcM [Type]
expandTheta tys =
  do full <- loop [] tys
     traceTc "expandTheta, full = " $ ppr full
     trim <- remove_immediate_super full
     trim_w_orig <- restore_original trim
     traceTc "expandTheta, trim = " $ ppr trim
     return trim_w_orig
  where
  loop ts [] = return ts
  loop ts frontier = do
    let all = ts ++ frontier
    ts' <- expandThetaMO_step frontier
    ts'' <- expandThetaSC_step frontier
    let new_frontier = filter ( not . (elemBy eqType all) ) (ts' ++ ts'')
    loop all new_frontier

  remove_immediate_super cts =
    do scs <- expandThetaSC_step cts
       case partition (elemBy eqType scs) cts of
         ([], cts) -> return cts
         (_, cts') -> remove_immediate_super cts' -- I think it's useless to loop

  restore_original cts =
    do let (_, cts') = partition (elemBy eqType cts) tys
       return (cts ++ cts')
---------------
-- One step of expanding the context with morphisms
expandThetaMO_step :: [Type] -> TcM [Type]
expandThetaMO_step tys = do
  let split_tys = catMaybes $ map getClassPredTys_maybe tys
  split_tys' <- concatMapM mapply_ctx split_tys
  let new_tys = flip map split_tys' (\(cl, ts) -> mkTyConApp (classTyCon cl) ts)
  return new_tys

  where
  mapply_ctx :: (Class, [Type])  -> TcM [(Class, [Type])]
  mapply_ctx (cls, tys) =
    do env <- getGblEnv
       eps <- getEps
       let ms = eps_morphs_env eps ++ tcg_morphs_env env
       let ms' = filter ( (cls==) . mAnt ) ms
       let new = flip map ms' (\minfo -> (mCon minfo, tys))
       return new

-- One step of expanding the context with its immediate superclasses
expandThetaSC_step :: [Type] -> TcM [Type]
expandThetaSC_step tys = do
  let split_tys = catMaybes $ map getClassPredTys_maybe tys
  superclasses <- concatMapM get_supercls split_tys
  let new_tys = flip map superclasses (\(cl, ts) -> mkTyConApp (classTyCon cl) ts)
  return new_tys

  where
  get_supercls :: (Class, [Type]) -> TcM [(Class, [Type])]
  get_supercls (cls, [ty]) = -- Hace falta revisar que no sea una abstract class?
    case classTyVars cls of
      [v] -> do traceTc "get_supercls" $ ppr (cls, ty)
                let superclasses = substTysWith [v] [ty] $ classSCTheta cls
                traceTc "Tys of: " $ ppr cls <+> text " -----> " <+> ppr ty
                traceTc "Superclasses of: " $ ppr cls <+> text " -----> " <+> ppr superclasses
                let split_superclasses = catMaybes $ map getClassPredTys_maybe superclasses
                let valid_superclasses = filter (\(_, tys') -> eqTypes [ty] tys') split_superclasses
                traceTc "Valid superclasses of: " $ ppr cls <+> text " -----> " <+> ppr valid_superclasses
                return valid_superclasses
      _ -> return []
  get_supercls _ = return []

expandTy :: Type -> TcM Type
expandTy ty =
    do let (tyvs, theta, cod) = tcSplitSigmaTyBndrs ty
       theta' <- expandTheta theta
       return $ mkSigmaTy tyvs theta' cod

expandSig :: TcIdSigInfo -> TcM TcIdSigInfo
expandSig (sig@(CompleteSig { sig_bndr = id })) =
    do ty' <- expandTy (varType id)
       traceTc "expandSig" $ ppr (varType id, ty')
       return $ sig { sig_bndr = updateVarType (\_ -> ty') id }

expandSig sig =
    do traceTc "expandSig default" $ ppr sig
       return sig

---------------------------------------------
-- i1 > i2 iff i1 `more_general` i2
moreGeneral :: ClsInstMorph
            -> ClsInstMorph
            -> TcM Bool
moreGeneral ( ClsInstMorph { info_cls = i1 } )
            ( ClsInstMorph { info_cls = i2 } ) =
  do let (_, theta1, ty1) = tcSplitSigmaTy (varType (is_dfun i1))
     let (_, theta2, ty2) = tcSplitSigmaTy (varType (is_dfun i2))
     res <- case tcMatchTy ty1 ty2 of
              Nothing -> return False
              Just s  -> do l <- expandThetaSC (substTys s theta1)
                            r <- expandThetaSC theta2
                            return $ l `is_subset` r
     when res $ traceTc "" $ ppr i1 <+> text " more general than " <+> ppr i2
     return res
  where is_subset xs ys = all (elemBy eqType ys) xs

strictlyMoreGeneral :: ClsInstMorph -> ClsInstMorph -> TcM Bool
strictlyMoreGeneral i1 i2 =
    do liftM2 (&&) (moreGeneral i1 i2) (liftM not (moreGeneral i2 i1))

maximals :: Monad m => (a -> a -> m Bool) -> [a] -> m [a]
maximals gt es =
    foldM insert [] es where

    insert es e = do b <- anyM (\e' -> gt e' e) es
                     if b
                     then return es
                     else do l <- filterM (\y -> liftM not $ gt e y) es
                             return (e:l)

shadowed :: ClsInstMorph -> [ClsInstMorph] -> TcM Bool
shadowed i is = anyM (flip moreGeneral i) is

keep_unshadowed :: [ClsInstMorph] -> [ClsInstMorph] -> TcM [ClsInstMorph]
keep_unshadowed is os = filterM (\i -> liftM not $ shadowed i os) is

mapply :: Morph
       -> ClsInstMorph
       -> TcM (Maybe ClsInstMorph)
mapply m@(Morph { mAnt = ant
                , mCon = con
                , mDFun = _ })
       (ClsInstMorph { info_cls = ispec })
    | ant /= is_cls ispec =
        return Nothing

    | otherwise = do
        let (d_tyvs, d_theta, _, d_tys) = tcSplitDFunTy (varType (is_dfun ispec))
        (sfresh, tyvs) <- freshenTyVarBndrs d_tyvs
        let theta = substTys sfresh d_theta
        let tys   = substTys sfresh d_tys

        -- FIXME: Use span for the morphism? Needs some refactoring.
        dfun_name <- newDFunName con tys noSrcSpan
        let dfun = mkDictFunId dfun_name tyvs theta con tys

        let new_spec = ispec { is_cls       = con
                             , is_cls_nm    = className con
                             , is_dfun      = dfun
                             , is_tvs       = tyvs
                             , is_tys       = tys
                             , is_dfun_name = tyVarName dfun
                             }
        let new_cinfo = ClsInstMorph { info_cls = new_spec
                                     , info_morph = Just m
                                     , ant_dfun = Just $ is_dfun ispec}
        traceTc "mapply applied: " $ vcat [ppr m, ppr ispec, ppr new_spec]

        return $ Just new_cinfo

closure_step :: [Morph] -> [ClsInstMorph] -> TcM [ClsInstMorph]
closure_step ms is =
    do cims <- sequence [mapply m i | m <- ms, i <- is ]
       return (catMaybes cims)

instance_closure :: [Morph] -> [ClsInstMorph] -> TcM [ClsInstMorph]
instance_closure ms is =
    do ns <- closure_step ms is
       cls <- loop [] ns
       traceTc "instance_closure, all derived instances:" $ ppr cls
       new <- keep_unshadowed cls is
       traceTc "instance_closure, unshadowed instances:" $ ppr new
       maxs <- maximals strictlyMoreGeneral new
       traceTc "instance_closure, maximal instances:" $ ppr maxs
       return maxs
    where
    loop vs [] = return vs
    loop vs frontier =
        do let all = vs ++ frontier ++ is
           new_frontier' <- closure_step ms frontier
           new_frontier <- keep_unshadowed new_frontier' all
           loop all new_frontier


-- Checking for ill-formed morphisms.
-- We consider a morphism ill if there's no way to generically obtain an
-- instance for the consequent's superclasses.
--
-- For example, this should fail:
-- |  instance A a
-- |  instance C a => B a
-- |  morphism A -> B
--
-- Unless we add at least one of these morphisms
-- | morphism B -> C
-- | morphism A -> C
--
-- TODO: we are doing this step only when all morphisms are in-scope.
-- Given the dependency analysis, it might just work to do it for each
-- one.
checkMorphWF :: Morph -> TcM ()
checkMorphWF m@(Morph { mDFun = dfun_m }) =
    do traceTc "checkMorphWF" $ ppr m
       let (_, co:an:_, _) = tcSplitSigmaTy (varType dfun_m) -- FIX ME
       scs_con <- expandThetaSC_step [co]
       scs_ant <- expandThetaSC [an]

       let is_upward_morph = elemBy eqType scs_ant co

       scs_ant' <- if is_upward_morph then return [an] else return scs_ant

       scs_ant'' <- expandThetaMO scs_ant'

       -- If any SC of the consequentis not on the computed set, fail
       flip mapM_ scs_con (\ct ->
           unless (elemBy eqType scs_ant'' ct) $
            setSrcSpan ( getSrcSpan dfun_m ) $
             addErrCtxt ( morphDeclCtxt2 m ) $
              addErrCtxt ( generically_scs co ct ) $
               failWithTc $ text "Bad morphism declaration")
   where
    generically_scs :: Type -> Type -> SDoc
    generically_scs c sc = text "No generic way to obtain an instance for the"
                            <+> ppr sc
                            <+> text "superclass of"
                            <+> ppr c
    morph_decl_ctxt :: SDoc -> SDoc
    morph_decl_ctxt doc = hang (text "In the morphism declaration")
                            2 (quotes doc)
    morphDeclCtxt2 :: Morph -> SDoc
    morphDeclCtxt2 morph
        = morph_decl_ctxt (ppr morph)

---------------------------------------------
-- Putting it all together
cover :: TcM [ClsInstMorph]
cover =
    do env <- getGblEnv
       eps <- getEps

       let all_morphs = eps_morphs_env eps ++ tcg_morphs_env env
       mapM_ checkMorphWF all_morphs

       InstEnvs { ie_global = gbl , ie_local = lcl } <- tcGetInstEnvs
       let all_insts = instEnvElts gbl ++ instEnvElts lcl

       traceTc "in cover, morphs = " $ ppr all_morphs
       traceTc "in cover, insts  = " $ ppr all_insts

       all_insts <- return $ map mkClsInstInfo all_insts
       all_insts <- instance_closure all_morphs all_insts
       return all_insts
    where
    mkClsInstInfo :: ClsInst -> ClsInstMorph
    mkClsInstInfo cls = ClsInstMorph { info_cls = cls
                                     , info_morph = Nothing
                                     , ant_dfun = Nothing}
