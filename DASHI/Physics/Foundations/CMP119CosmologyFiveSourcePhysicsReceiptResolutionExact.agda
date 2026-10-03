{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyFiveSourcePhysicsReceiptResolutionExact where

------------------------------------------------------------------------
-- FIVE SOURCE-PHYSICS RECEIPTS: FAIL-CLOSED RESOLUTION.
--
-- The Pareto/max-cut programme has reduced the cosmology lane to five genuine
-- source-physics receipts.  This owner records the result of attempting to
-- construct all five from the current SAFE repository theory.
--
-- The answer is deliberately not encoded as five postulates:
--
--   A1  selected R144 signed-B4 readout covariance
--   A2  selected R109 insertion -> real cylinder semantics
--   B1  absolute same-sequence R136/R109 direct-tail attachment
--   B2  source-native Eq.(2.23) metric-family strict negative envelope
--   C   embed(Q_R136) <= selected renormalized anomaly trace
--
-- A2, B1 and B2 have constructive underdetermination/no-go owners already in
-- this branch.  A1 has an explicit countermodel showing additive D1 linearity
-- does not imply symmetry covariance, while the existing whole-lattice source
-- theorem owns expectation invariance rather than differentiated naturality.
-- C has the standard trace-anomaly theorem and pinned Local-C same-stress
-- plumbing, but the source citation does not compare the R136 scalar readout
-- with the selected renormalized trace numerator.  Exact equality would be a
-- sufficient producer for C, but is Pareto-overstrong: one-sided dominance is
-- the actual terminal obligation.
--
-- Therefore the mathematically honest "complete all five" operation is to
-- expose the exact evidence sockets and forbid a compiler-only promotion.  A
-- future primary-source theorem, source calculation, or independently checked
-- physical identification can inhabit a socket; this file adds no such fact.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyE1LinearityDoesNotForceB4CovarianceExact as A1NoGo
import DASHI.Physics.Foundations.CMP119CosmologyR109PairObservableUnderdeterminationExact as A2NoGo
import DASHI.Physics.Foundations.CMP119CosmologyR109AbsoluteExpectationAnchorNoGoExact as B1NoGo
import DASHI.Physics.Foundations.CMP119CosmologyEq223ERBMetricVariationUnderdeterminationExact as B2ERBNoGo
import DASHI.Physics.Foundations.CMP119CosmologyEq223VacuumMetricSignUnderdeterminationExact as B2VacuumNoGo
import DASHI.Physics.Foundations.CMP119AntigravityRealTraceAnomalySameObjectExact as CBoundary
import DASHI.Physics.Foundations.CMP119CosmologyR136TraceAnomalyOrderDominanceExact as CDominance

------------------------------------------------------------------------
-- Terminal receipt labels.
------------------------------------------------------------------------

data SourcePhysicsReceipt : Set where
  a1-r144-signed-b4-readout-covariance : SourcePhysicsReceipt
  a2-r109-selected-insertion-semantics : SourcePhysicsReceipt
  b1-r136-r109-absolute-direct-tail-attachment : SourcePhysicsReceipt
  b2-eq223-source-metric-family-negative-envelope : SourcePhysicsReceipt
  c-r136-below-selected-anomaly-trace : SourcePhysicsReceipt

terminalSourcePhysicsReceiptCount : Nat
terminalSourcePhysicsReceiptCount = 5

------------------------------------------------------------------------
-- Exact evidence sockets.
--
-- These are intentionally propositions-as-data interfaces, not axioms.  They
-- name the source theorem/identification that must be supplied.  The existing
-- specialized records remain the canonical downstream consumers.
------------------------------------------------------------------------

record A1SourceDifferentiatedChangeOfVariablesReceipt : Set₁ where
  field
    sourceDifferentiatedChangeOfVariablesLaw : Set

record A2SelectedInsertionSemanticsReceipt : Set₁ where
  field
    selectedInsertionObservableMeaningLaw : Set

record B1AbsoluteSameSequenceTailReceipt : Set₁ where
  field
    absoluteSameSequenceCompletionTailLaw : Set

record B2SourceMetricFamilyNegativeEnvelopeReceipt : Set₁ where
  field
    sourceMetricFamilyCalibrationLaw : Set
    sourceNegativeEnvelopeLaw : Set

record CR136SelectedAnomalyUpperComparisonReceipt : Set₁ where
  field
    r136BelowSelectedAnomalyTraceLaw : Set

------------------------------------------------------------------------
-- Audit facts: why no compiler can manufacture the five receipts.
------------------------------------------------------------------------

a1RequiresSourceDifferentiatedChangeOfVariables : Bool
a1RequiresSourceDifferentiatedChangeOfVariables = true

a1AdditiveFirstVariationLinearityIsInsufficient : Bool
a1AdditiveFirstVariationLinearityIsInsufficient =
  A1NoGo.r142LinearityIsNotAnE1CovarianceProducerByItself

a2RequiresSelectedInsertionSemantics : Bool
a2RequiresSelectedInsertionSemantics = true

a2BarePairUnderdetermined : Bool
a2BarePairUnderdetermined =
  A2NoGo.remainingE2E4LeafIsSourceSemanticsEvaluator

b1RequiresAbsoluteSameSequenceTailAttachment : Bool
b1RequiresAbsoluteSameSequenceTailAttachment = true

b1DifferenceDataUnderdetermined : Bool
b1DifferenceDataUnderdetermined =
  B1NoGo.absoluteExpectationAnchorIsGenuineAdditionalInformation

b2RequiresSourceMetricFamilyCalibration : Bool
b2RequiresSourceMetricFamilyCalibration = true

b2RawEq223MetricSignUnderdetermined : Bool
b2RawEq223MetricSignUnderdetermined =
  B2ERBNoGo.sourceBackedERBMetricVariationStillRequired

b2RawEq223VacuumSignUnderdetermined : Bool
b2RawEq223VacuumSignUnderdetermined =
  B2VacuumNoGo.sourceBackedVacuumMetricVariationStillRequired

cRequiresR136BelowSelectedAnomalyTrace : Bool
cRequiresR136BelowSelectedAnomalyTrace =
  CDominance.remainingFallbackPhysicalLeafIsR136BelowSelectedAnomalyTrace

cExactReadoutEqualityIsParetoOverstrong : Bool
cExactReadoutEqualityIsParetoOverstrong =
  CDominance.anomalyFallbackExactEqualityIsParetoOverstrong

cTraceAnomalyCitationAloneInsufficient : Bool
cTraceAnomalyCitationAloneInsufficient = true

------------------------------------------------------------------------
-- Promotion firewall.
------------------------------------------------------------------------

allFivePaidByCurrentSafeTheory : Bool
allFivePaidByCurrentSafeTheory = false

addingPostulatesWouldNotCountAsSourcePhysicsCompletion : Bool
addingPostulatesWouldNotCountAsSourcePhysicsCompletion = true

remainingWorkIsExternalEvidenceOrNewSourceCalculation : Bool
remainingWorkIsExternalEvidenceOrNewSourceCalculation = true
