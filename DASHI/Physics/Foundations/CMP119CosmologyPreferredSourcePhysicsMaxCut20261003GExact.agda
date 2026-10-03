{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredSourcePhysicsMaxCut20261003GExact where

------------------------------------------------------------------------
-- PREFERRED SOURCE-PHYSICS MAX-CUT / OVERLAY G / 2026-10-03.
--
-- This owner removes the stale accounting in which the alternate anomaly lane
-- was counted together with the preferred Eq.(2.23) route.  On the preferred
-- route there are exactly FOUR model-specific source payments:
--
--   A1  selected R144 signed-B4 finite-D1 covariance;
--   A2  selected R109 insertion -> the one actual Wilson/OS-admissible
--       cylinder presentation;
--   B1  the SAME pinned finite expectation family carries both
--         F_k = embed(DGamma_k)
--       and
--         embed(Q_R136) <= F_k + embed(Tail_109(k));
--   B2  quantitative source negativity strong enough to beat Tail_109(k).
--
-- The Eq.(2.23) coordinate realization of B2 is
--
--   c_V < -(M_ERB + Tail_109(k)),
--
-- where M_ERB is one combined E/R/B envelope.  A newer canonical-source lane
-- already compiles the selected source anchor + ordered Haar/SU(2) trace data
-- to STRICT finite diagonal negativity.  Therefore "prove any negative sign"
-- is no longer the B2 frontier; the surviving strength is the quantitative
-- tail-beating margin.
--
-- All arithmetic/order transport below B1+B2 is already compiler-owned by the
-- concrete R109-tail -> R136 -> terminal-acceleration route.  A1/A2 belong to
-- reconstruction/source semantics.  Standard marked-OS reconstruction remains
-- an external/standard boundary and is NOT charged as a fifth model-specific
-- source payment.  Likewise the anomaly-dominance lane is a fallback, not a
-- fifth premise of this preferred route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyE1R144CanonicalB4ReadoutExact as A1
import DASHI.Physics.Foundations.CMP119CosmologyR109SelectedStressCylinderPresentationExact as A2
import DASHI.Physics.Foundations.CMP119CosmologyConcreteFiniteR109RealCompletionExact as B1Completion
import DASHI.Physics.Foundations.CMP119CosmologyEq223ConcreteR109TailToR136Exact as B1Concrete
import DASHI.Physics.Foundations.CMP119CosmologyEq223CombinedERBEnvelopeMaxCutExact as B2Envelope
import DASHI.Physics.Foundations.CMP119CosmologyEq223VacuumTailThresholdExact as B2Threshold
import DASHI.Physics.Foundations.CMP119CanonicalSourceOrderedHaarTraceClosureExact as CanonicalTrace
import DASHI.Physics.Foundations.CMP119CosmologyEq223ConcreteVacuumThresholdToExpansionExact as Terminal
import DASHI.Physics.Foundations.CMP119CosmologyLatestParetoFrontierExact as Prior

data PreferredSourcePhysicsResidual : Set where
  a1-r144-canonical-b4-signed-readout-covariance :
    PreferredSourcePhysicsResidual

  a2-selected-r109-stress-insertion-presentation :
    PreferredSourcePhysicsResidual

  b1-concrete-pinned-r109-completion-and-finite-attachment :
    PreferredSourcePhysicsResidual

  b2-quantitative-source-negativity-beats-r109-tail :
    PreferredSourcePhysicsResidual

preferredSourcePhysicsResidualCount : Nat
preferredSourcePhysicsResidualCount = 4

------------------------------------------------------------------------
-- A1.
------------------------------------------------------------------------

a1IsOneCanonicalR144B4SourceTheorem : Bool
a1IsOneCanonicalR144B4SourceTheorem = true

a1GeneratorAttachmentIsAlreadyCanonical : Bool
a1GeneratorAttachmentIsAlreadyCanonical =
  A1.canonicalB4GeneratorAttachmentIsIdentity

a1NeedsNoIndependentGeneratorToEuclideanActionMap : Bool
a1NeedsNoIndependentGeneratorToEuclideanActionMap =
  A1.noIndependentGeneratorToEuclideanActionMap

a1AdditiveLinearityAloneIsNotPayment : Bool
a1AdditiveLinearityAloneIsNotPayment = true

------------------------------------------------------------------------
-- A2.
------------------------------------------------------------------------

a2IsOneSelectedR109InsertionPresentation : Bool
a2IsOneSelectedR109InsertionPresentation = true

a2NeedsNoGlobalPairEvaluator : Bool
a2NeedsNoGlobalPairEvaluator =
  A2.selectedPresentationRequiresGlobalPairEvaluator

a2PublishedOSPredicatesAlreadyPinned : Bool
a2PublishedOSPredicatesAlreadyPinned =
  A2.publishedOSAdmissibilityPredicatesPinned

a2RemainingPhysicalContentIsSelectedInsertionSemantics : Bool
a2RemainingPhysicalContentIsSelectedInsertionSemantics =
  A2.selectedStressInsertionSemanticsStillPhysical

------------------------------------------------------------------------
-- B1.
------------------------------------------------------------------------

b1UsesConcretePinnedFiniteExpectationFamily : Bool
b1UsesConcretePinnedFiniteExpectationFamily =
  B1Completion.arbitraryFiniteExpectationSequenceEliminated

b1ArbitraryFiniteSequenceStillCharged : Bool
b1ArbitraryFiniteSequenceStillCharged = false

b1FiniteSameObjectLeafIsPinnedExpectationEqualsDGamma : Bool
b1FiniteSameObjectLeafIsPinnedExpectationEqualsDGamma =
  B1Concrete.remainingB1FiniteSameObjectLeafIsPinnedExpectationEqualsDGamma

b1CompletionLeafIsConcreteSameSequenceTailBound : Bool
b1CompletionLeafIsConcreteSameSequenceTailBound =
  B1Concrete.remainingB1CompletionLeafIsConcreteSameSequenceTailBound

b1IsOnePackagedConcreteScaleAnchor : Bool
b1IsOnePackagedConcreteScaleAnchor = true

------------------------------------------------------------------------
-- B2.
------------------------------------------------------------------------

b2IsCombinedERBEnvelopePlusLiteralVacuumThreshold : Bool
b2IsCombinedERBEnvelopePlusLiteralVacuumThreshold = true

b2ThreeSeparateSectorCalibrationsAreNotTerminal : Bool
b2ThreeSeparateSectorCalibrationsAreNotTerminal =
  B2Envelope.combinedERBEnvelopeReplacesThreeTerminalSectorBounds

b2TailIsPartOfLiteralVacuumBudget : Bool
b2TailIsPartOfLiteralVacuumBudget =
  B2Threshold.round109TailIsPartOfRequiredVacuumBudget

b2CanonicalSourceCanAlreadyCompileStrictFiniteTraceNegativity : Bool
b2CanonicalSourceCanAlreadyCompileStrictFiniteTraceNegativity =
  CanonicalTrace.canonicalSourceEqualityCompilesToFiniteTraceNegativity

b2FiniteNegativityAloneDoesNotPayTailMargin : Bool
b2FiniteNegativityAloneDoesNotPayTailMargin =
  CanonicalTrace.finiteTraceNegativityAlonePaysR109TailMargin

b2RemainingPreferredSignStrengthIsQuantitativeTailMargin : Bool
b2RemainingPreferredSignStrengthIsQuantitativeTailMargin =
  CanonicalTrace.remainingPreferredSignStrengthIsQuantitativeTailMargin

b2RawEq223SourceAloneDoesNotFixThreshold : Bool
b2RawEq223SourceAloneDoesNotFixThreshold = true

------------------------------------------------------------------------
-- Accounting / downstream closure.
------------------------------------------------------------------------

preferredRouteChargesAnomalyFallbackAsFifthLeaf : Bool
preferredRouteChargesAnomalyFallbackAsFifthLeaf = false

alternateAnomalyLaneStillAvailableButNotPreferredPremise : Bool
alternateAnomalyLaneStillAvailableButNotPreferredPremise = true

standardOSReconstructionBoundaryIsSeparateFromFourSourcePayments : Bool
standardOSReconstructionBoundaryIsSeparateFromFourSourcePayments = true

preferredFourPaymentsCompileThroughExistingTerminalArchitecture : Bool
preferredFourPaymentsCompileThroughExistingTerminalArchitecture =
  Terminal.preferredConcreteVacuumThresholdCompilesToMatterAcceleration

preferredRouteNeedsFiniteEqualsContinuumEquality : Bool
preferredRouteNeedsFiniteEqualsContinuumEquality =
  Terminal.preferredConcreteVacuumThresholdRouteNeedsFiniteEqualsContinuum

priorFiveLeafCountIncludedAlternateFallback : Bool
priorFiveLeafCountIncludedAlternateFallback = true

preferredRouteSourcePhysicsIsAdapterComplete : Bool
preferredRouteSourcePhysicsIsAdapterComplete = true

preferredRouteSourcePhysicsIsEvidenceComplete : Bool
preferredRouteSourcePhysicsIsEvidenceComplete = false
