{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityEq223ConcreteTailReuseMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119AntigravityEq223MetricStressReuseMaxCutExact as Legacy
import DASHI.Physics.Foundations.CMP119CosmologyEq223ConcreteR109TailToR136Exact as Concrete
import DASHI.Physics.Foundations.CMP119CosmologyB1SelectedSameSequenceMaxCutExact as B1
import DASHI.Physics.Foundations.CMP119CosmologyPrimarySourceScopeAudit20261004Exact as Audit

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
-- The primary-source audit also classifies the lower B1 inputs as SOURCE
-- THEOREMS rather than missing adapters.  Therefore this recut is a stopping
-- rule as well as a scheduler: further closure requires proving new same-object
-- mathematics/source semantics, not adding another transport layer.
------------------------------------------------------------------------

preferredConcreteTailRouteNeedsExactFiniteContinuumEquality : Bool
preferredConcreteTailRouteNeedsExactFiniteContinuumEquality =
  Concrete.preferredConcreteTailRouteNeedsFiniteEqualsContinuum

preferredConcreteTailRouteEliminatesExactFiniteContinuumEquality : Bool
preferredConcreteTailRouteEliminatesExactFiniteContinuumEquality = true

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

------------------------------------------------------------------------
-- LOWER B1 SOURCE BOUNDARY
------------------------------------------------------------------------

round109FiniteTailSemanticsIsSourceTheorem : Bool
round109FiniteTailSemanticsIsSourceTheorem =
  B1.round109FiniteTailSemanticsIsSourceLeaf

completionEndpointIdentityIsSourceTheorem : Bool
completionEndpointIdentityIsSourceTheorem =
  B1.completionEndpointIdentityIsSourceLeaf

allCutoffR144FiniteAttachmentIsSourceTheorem : Bool
allCutoffR144FiniteAttachmentIsSourceTheorem =
  B1.allCutoffR144FiniteAttachmentIsSourceLeaf

remainingAdapterConstructionCount : Nat
remainingAdapterConstructionCount = Audit.remainingAdapterConstructionCount

currentImportedPrimarySourceClosesAllIrreducibleCosmologyTheorems : Bool
currentImportedPrimarySourceClosesAllIrreducibleCosmologyTheorems =
  Audit.currentPrimarySourceSurfaceClosesAllIrreducibleCosmologyTheorems

claimingSourceLeavesClosedWithoutNewMathematicsWouldOverpromote : Bool
claimingSourceLeavesClosedWithoutNewMathematicsWouldOverpromote =
  Audit.claimingAllSixClosedFromCurrentImportedSourceWouldAddNewMathematics

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
    lowerB1InputsAreSourceTheoremsNotAdapterDebt : Bool
    remainingAdapterConstructionDebt : Nat

canonicalEq223ConcreteTailReuseBoundary : Eq223ConcreteTailReuseBoundary
canonicalEq223ConcreteTailReuseBoundary =
  eq223-concrete-tail-reuse-boundary
    true true true false true true true true false true
    remainingAdapterConstructionCount

preferredR136RouteIsConcreteSameSequenceTailRoute : Bool
preferredR136RouteIsConcreteSameSequenceTailRoute = true

noContinuumEqualityPromotedByThisRecut : Bool
noContinuumEqualityPromotedByThisRecut = true
