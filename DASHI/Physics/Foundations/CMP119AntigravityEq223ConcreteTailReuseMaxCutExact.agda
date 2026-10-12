{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityEq223ConcreteTailReuseMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.Foundations.CMP119AntigravityEq223MetricStressReuseMaxCutExact as Legacy
import DASHI.Physics.Foundations.CMP119CosmologyEq223ConcreteR109TailToR136Exact as Concrete

------------------------------------------------------------------------
-- ANTIGRAVITY R136 RECUT THROUGH THE CONCRETE R109 SAME-SEQUENCE TAIL ROUTE
--
-- The older antigravity reuse boundary exposed a direct exact equality
--
--   Q_R136 = finite matter-effective-action Weyl response
--
-- as the remaining same-object payment.  Current master owns a strictly weaker
-- and therefore preferable concrete route.  At one selected cutoff it requires
-- only
--
--   finiteExpectation_k = embed(D_Gamma,k^Weyl)
--
-- together with the concrete SAME-SEQUENCE R109 completion/tail bound.  A
-- strict finite+tail source margin then implies Q_R136 < 0.  The concrete owner
-- explicitly does NOT require an exact finite-cutoff = continuum equality.
--
-- This file changes proof scheduling only.  It does not manufacture the pinned
-- finite expectation anchor, the tail/completion receipt, or the strict source
-- margin.
------------------------------------------------------------------------

preferredConcreteTailRouteEliminatesExactFiniteContinuumEquality : Bool
preferredConcreteTailRouteEliminatesExactFiniteContinuumEquality =
  Concrete.preferredConcreteTailRouteNeedsFiniteEqualsContinuum

-- The imported flag is phrased "needs equality" and is false.  Export a
-- positive-polarity scheduler flag as well.
exactFiniteContinuumEqualityRequiredOnPreferredConcreteTailRoute : Bool
exactFiniteContinuumEqualityRequiredOnPreferredConcreteTailRoute = false

pinnedExpectationEqualsDGammaStillRequired : Bool
pinnedExpectationEqualsDGammaStillRequired =
  Concrete.remainingB1FiniteSameObjectLeafIsPinnedExpectationEqualsDGamma

concreteSameSequenceTailBoundStillRequired : Bool
concreteSameSequenceTailBoundStillRequired =
  Concrete.remainingB1CompletionLeafIsConcreteSameSequenceTailBound

strictFinitePlusTailMarginStillRequired : Bool
strictFinitePlusTailMarginStillRequired = true

legacyDirectResponseEqualityStillAvailableButNotShortestPath : Bool
legacyDirectResponseEqualityStillAvailableButNotShortestPath =
  Legacy.sameObjectEffectiveActionResponseWeldExists

record Eq223ConcreteTailReuseBoundary : Set where
  constructor eq223-concrete-tail-reuse-boundary
  field
    literalEq223MetricVariationAlreadyOwned : Bool
    concreteR109FiniteFamilyAlreadyOwned : Bool
    concreteR109ToR136TailCompilerAlreadyOwned : Bool
    exactFiniteEqualsContinuumRequired : Bool
    selectedFiniteExpectationEqualsDGammaRequired : Bool
    concreteSameSequenceCompletionTailRequired : Bool
    strictFinitePlusTailSourceMarginRequired : Bool
    legacyDirectEqualitySurfaceStillExists : Bool
    legacyDirectEqualityIsShortestPreferredPayment : Bool

canonicalEq223ConcreteTailReuseBoundary : Eq223ConcreteTailReuseBoundary
canonicalEq223ConcreteTailReuseBoundary =
  eq223-concrete-tail-reuse-boundary
    true true true false true true true true false

preferredR136RouteIsConcreteSameSequenceTailRoute : Bool
preferredR136RouteIsConcreteSameSequenceTailRoute = true

noContinuumEqualityPromotedByThisRecut : Bool
noContinuumEqualityPromotedByThisRecut = true
