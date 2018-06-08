module TcIface where

import GhcPrelude
import IfaceSyn    ( IfaceDecl, IfaceClsInst, IfaceMorph, IfaceFamInst, IfaceRule,
                     IfaceAnnotation, IfaceCompleteMatch )
import TyCoRep     ( TyThing )
import TcRnTypes   ( IfL )
import InstEnv     ( ClsInst, Morph )
import FamInstEnv  ( FamInst )
import CoreSyn     ( CoreRule )
import HscTypes    ( CompleteMatch )
import Annotations ( Annotation )

tcIfaceDecl         :: Bool -> IfaceDecl -> IfL TyThing
tcIfaceRules        :: Bool -> [IfaceRule] -> IfL [CoreRule]
tcIfaceInst         :: IfaceClsInst -> IfL ClsInst
tcIfaceMorph        :: IfaceMorph -> IfL Morph
tcIfaceFamInst      :: IfaceFamInst -> IfL FamInst
tcIfaceAnnotations  :: [IfaceAnnotation] -> IfL [Annotation]
tcIfaceCompleteSigs :: [IfaceCompleteMatch] -> IfL [CompleteMatch]
