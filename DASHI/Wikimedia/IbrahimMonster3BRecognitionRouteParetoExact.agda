module DASHI.Wikimedia.IbrahimMonster3BRecognitionRouteParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimMonster3BConstituentAttachmentSnowballExact as Constituent
import DASHI.Wikimedia.IbrahimMonster3BWholeCharacterIsotypicBypassExact as Whole
import DASHI.Wikimedia.IbrahimMonster3BCharacterExecutionCutsetSnowballExact as Cutset

------------------------------------------------------------------------
-- RECOGNITION ROUTE PARETO SELECTOR
--
-- Two theorem-bearing routes now coexist after the same actual-kernel replay.
--
--   constituent route:
--     actual W_zeta|E -> literal simple constituents -> classify each by
--     selected central phase / equal irreducible character -> 90 H_zeta.
--
--   whole-character route:
--     chi(W_zeta|E)=90 chi(H_zeta) + Maschke/isotypic assembly ->
--     whole equivariant isomorphism W_zeta|E ~= H_zeta^90.
--
-- Neither route Pareto-dominates the other before execution.  The whole route
-- removes a Monster-specific literal constituent enumeration, but adds one
-- stronger generic semisimple/isotypic producer that has not yet been written
-- or kernel-checked.  We therefore keep both and probe the whole-character
-- route first because a cheap generic theorem would collapse more downstream
-- same-object bookkeeping.
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

------------------------------------------------------------------------
-- Existing owners remain authoritative for each leaf.
------------------------------------------------------------------------

constituentFrontier : Constituent.ConstituentAttachmentFrontier
constituentFrontier = Constituent.currentConstituentAttachmentFrontier

wholeCharacterFrontier : Whole.WholeCharacterIsotypicBypassBoundary
wholeCharacterFrontier = Whole.canonicalWholeCharacterIsotypicBypassBoundary

executionFrontier : Cutset.Monster3BCharacterExecutionFrontier
executionFrontier = Cutset.currentMonster3BCharacterExecutionFrontier

------------------------------------------------------------------------
-- WrongType boundaries.
------------------------------------------------------------------------

data SearchPriorityCreatesProof : Set where
data RoutePreferenceCreatesExecutionReceipt : Set where
data OEISSelectsRepresentationProofRoute : Set where
data DimensionClosesRepresentationRoute : Set where

searchPriorityDoesNotCreateProof : SearchPriorityCreatesProof → ⊥
searchPriorityDoesNotCreateProof ()

routePreferenceDoesNotCreateReceipt : RoutePreferenceCreatesExecutionReceipt → ⊥
routePreferenceDoesNotCreateReceipt ()

oeisDoesNotSelectRepresentationRoute : OEISSelectsRepresentationProofRoute → ⊥
oeisDoesNotSelectRepresentationRoute ()

dimensionDoesNotCloseRoute : DimensionClosesRepresentationRoute → ⊥
dimensionDoesNotCloseRoute ()

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
  false false false false
  false false
  "probe the whole-character route first: implement the smallest generic Lean semisimple/isotypic theorem at the pinned v4.28.0 dependency that turns char(V)=90*char(H), with H simple, into a whole equivariant isomorphism V ~= H^90. If that source route becomes awkward or requires more infrastructure than the existing constituent attachment, fall back immediately to the literal constituent route. In either case, actual MN3B kernel replay remains upstream and the concrete X6 x Fin90 / Base369 action weld remains downstream. OEIS A005052 and 65610=729*90 stay navigation/arithmetic only."
