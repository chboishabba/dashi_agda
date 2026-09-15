module DASHI.Wikimedia.IbrahimMonster3BRecognitionRouteParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerIndexedResidualRefinementExact as Refinement
import DASHI.Wikimedia.IbrahimMonster3BConstituentAttachmentSnowballExact as Constituent
import DASHI.Wikimedia.IbrahimMonster3BWholeCharacterIsotypicBypassExact as Whole
import DASHI.Wikimedia.IbrahimMonster3BCharacterExecutionCutsetSnowballExact as Cutset

------------------------------------------------------------------------
-- RECOGNITION ROUTE PARETO SELECTOR
--
-- Two theorem-bearing routes coexist after the same actual-kernel replay.
-- The whole-character probe has now localized one concrete implementation seam:
-- character evidence is on FDRep while the strongest isotypic assembly APIs are
-- group-algebra-module level.  That is not evidence against the theorem; it is
-- exactly the residual to test before paying the richer constituent route.
--
-- Bidi rule:
--   coarse whole-character route succeeds -> keep the cheaper consumer proof;
--   coarse route hits a real obstruction -> reopen constituent-level residual;
--   neither outcome licenses an automatic jump to the concrete X6 x Fin90
--   basis/action representation.
------------------------------------------------------------------------

data RecognitionRoute : Set where
  literalConstituentRoute : RecognitionRoute
  wholeCharacterIsotypicRoute : RecognitionRoute

record RecognitionRouteTradeoff : Set where
  constructor recognition-route-tradeoff
  field
    route : RecognitionRoute
    usesExistingIrreducibleCharacterWrapper : Bool
    needsNewStrongerGenericProducer : Bool
    needsLiteralConstituentEnumeration : Bool
    needsActualKernelReplay : Bool
    needsSameObjectMonsterAttachment : Bool
    stillNeedsConcreteBasisActionWeld : Bool
open RecognitionRouteTradeoff public

constituentTradeoff : RecognitionRouteTradeoff
constituentTradeoff = recognition-route-tradeoff
  literalConstituentRoute
  true false true true true true

wholeCharacterTradeoff : RecognitionRouteTradeoff
wholeCharacterTradeoff = recognition-route-tradeoff
  wholeCharacterIsotypicRoute
  true true false true true true

constituentFrontier : Constituent.ConstituentAttachmentFrontier
constituentFrontier = Constituent.currentConstituentAttachmentFrontier

wholeCharacterFrontier : Whole.WholeCharacterIsotypicBypassBoundary
wholeCharacterFrontier = Whole.canonicalWholeCharacterIsotypicBypassBoundary

executionFrontier : Cutset.Monster3BCharacterExecutionFrontier
executionFrontier = Cutset.currentMonster3BCharacterExecutionFrontier

refinementBoundary : Refinement.ConsumerIndexedResidualRefinementBoundary
refinementBoundary = Refinement.canonicalConsumerIndexedResidualRefinementBoundary

------------------------------------------------------------------------
-- WrongType boundaries.
------------------------------------------------------------------------

data SearchPriorityCreatesProof : Set where
data RoutePreferenceCreatesExecutionReceipt : Set where
data OEISSelectsRepresentationProofRoute : Set where
data DimensionClosesRepresentationRoute : Set where
data FailedCoarseRouteForcesConcreteBasisReconstruction : Set where

searchPriorityDoesNotCreateProof : SearchPriorityCreatesProof → ⊥
searchPriorityDoesNotCreateProof ()

routePreferenceDoesNotCreateReceipt : RoutePreferenceCreatesExecutionReceipt → ⊥
routePreferenceDoesNotCreateReceipt ()

oeisDoesNotSelectRepresentationRoute : OEISSelectsRepresentationProofRoute → ⊥
oeisDoesNotSelectRepresentationRoute ()

dimensionDoesNotCloseRoute : DimensionClosesRepresentationRoute → ⊥
dimensionDoesNotCloseRoute ()

failedCoarseRouteDoesNotForceConcreteBasis :
  FailedCoarseRouteForcesConcreteBasisReconstruction → ⊥
failedCoarseRouteDoesNotForceConcreteBasis ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record RecognitionRouteParetoBoundary : Set where
  constructor recognition-route-pareto-boundary
  field
    constituentRouteRetained : Bool
    wholeCharacterRouteRetained : Bool
    routesParetoIncomparableBeforeExecution : Bool
    wholeCharacterRouteHighestAlphaProbe : Bool
    literalConstituentEnumerationMandatory : Bool

    wholeCharacterInterfaceSeamLocalized : Bool
    failedCoarseRouteReopensConstituentResidual : Bool
    failedCoarseRouteForcesConcreteBasisReconstruction : Bool

    actualKernelReplayReceiptObserved : Bool
    wholeCharacterBypassKernelReceiptObserved : Bool
    literalConstituentAttachmentObserved : Bool
    actualActionRecognitionObserved : Bool

    oeisCanSelectRepresentationRouteByProofAuthority : Bool
    numericalDimensionCanCloseEitherRoute : Bool

    nextResidual : String
open RecognitionRouteParetoBoundary public

canonicalRecognitionRouteParetoBoundary : RecognitionRouteParetoBoundary
canonicalRecognitionRouteParetoBoundary = recognition-route-pareto-boundary
  true true true true false
  true true false
  false false false false
  false false
  "probe only the localized FDRep-to-group-algebra interface seam on the whole-character route. If a small adapter closes it, pursue the consumer-sufficient isotypic theorem. If the adapter exposes a substantive obstruction, reopen the literal constituent decomposition as the next residual. Do not jump directly from either failure or numerical equalities to the X6 x Fin90/Base369 basis-action representation. Actual MN3B replay remains upstream; same-object action recognition remains downstream; OEIS A005052 and 65610=729*90 remain navigation/arithmetic only."
