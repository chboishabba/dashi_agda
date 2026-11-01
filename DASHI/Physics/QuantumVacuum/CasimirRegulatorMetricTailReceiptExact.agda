module DASHI.Physics.QuantumVacuum.CasimirRegulatorMetricTailReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.MetricConvergenceKernelBidiExact as Metric

------------------------------------------------------------------------
-- COHERENT PROOF-BEARING REGULATOR TAIL RECEIPT
--
-- The older RegulatorTailEstimate stored a second copy of the Parameter,
-- Index, Value and Epsilon carriers beside `metricProblem`, without equalities
-- identifying those copies with the metric problem.  Consequently its
-- threshold formula was not definitionally a threshold for the metric family.
--
-- This owner removes that ambiguity.  All tail data are indexed directly by
-- one literal ParameterisedMetricLimitProblem.
------------------------------------------------------------------------

record ProofBearingMetricTail
    (P : Metric.ParameterisedMetricLimitProblem) : Set₁ where
  field
    threshold : Metric.Parameter P → Metric.Epsilon P → Metric.Index P

    tailClose :
      (parameter : Metric.Parameter P) →
      (epsilon : Metric.Epsilon P) →
      Metric.Positive P epsilon →
      (index : Metric.Index P) →
      Metric._≼_ P (threshold parameter epsilon) index →
      Metric.Close P
        (Metric.family P parameter index)
        (Metric.candidate P parameter)
        epsilon

    PresentationIndependent : Set
    presentationIndependentEvidence : PresentationIndependent

    reading : String

open ProofBearingMetricTail public

asPointwiseMetricConvergence :
  ∀ {P} →
  ProofBearingMetricTail P →
  Metric.PointwiseMetricConvergence P
asPointwiseMetricConvergence T = record
  { Metric.threshold = threshold T
  ; Metric.tailClose = tailClose T
  ; Metric.convergenceReading = reading T
  }

------------------------------------------------------------------------
-- Reverse proof search now asks for the actual dependent tail theorem.
------------------------------------------------------------------------

record ReverseMetricTailObligations
    (P : Metric.ParameterisedMetricLimitProblem) : Set₁ where
  field
    thresholdConstruction :
      Metric.Parameter P → Metric.Epsilon P → Metric.Index P

    literalTailEstimate :
      (parameter : Metric.Parameter P) →
      (epsilon : Metric.Epsilon P) →
      Metric.Positive P epsilon →
      (index : Metric.Index P) →
      Metric._≼_ P (thresholdConstruction parameter epsilon) index →
      Metric.Close P
        (Metric.family P parameter index)
        (Metric.candidate P parameter)
        epsilon

    presentationIndependence : Set
    sameLiteralMetricFamily : Set
    sameLiteralCandidate : Set
    reading : String

open ReverseMetricTailObligations public

data BareTailSetLabelAutomaticallySuppliesMetricConvergence : Set where

data DuplicateCarrierCopiesAutomaticallyMatchMetricProblem : Set where

bareLabelDoesNotSupplyTailProof :
  BareTailSetLabelAutomaticallySuppliesMetricConvergence → ⊥
bareLabelDoesNotSupplyTailProof ()

duplicateCarriersDoNotAutoWeld :
  DuplicateCarrierCopiesAutomaticallyMatchMetricProblem → ⊥
duplicateCarriersDoNotAutoWeld ()

record Status : Set where
  field
    singleMetricCarrierFamilyOwned : Bool
    dependentTailEstimateProofBearing : Bool
    pointwiseConvergenceCompilerOwned : Bool
    duplicateCarrierCopiesRequired : Bool

    singleMetricCarrierFamilyOwnedIsTrue : singleMetricCarrierFamilyOwned ≡ true
    dependentTailEstimateProofBearingIsTrue : dependentTailEstimateProofBearing ≡ true
    pointwiseConvergenceCompilerOwnedIsTrue : pointwiseConvergenceCompilerOwned ≡ true
    duplicateCarrierCopiesRequiredIsFalse : duplicateCarrierCopiesRequired ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { singleMetricCarrierFamilyOwned = true
  ; dependentTailEstimateProofBearing = true
  ; pointwiseConvergenceCompilerOwned = true
  ; duplicateCarrierCopiesRequired = false
  ; singleMetricCarrierFamilyOwnedIsTrue = refl
  ; dependentTailEstimateProofBearingIsTrue = refl
  ; pointwiseConvergenceCompilerOwnedIsTrue = refl
  ; duplicateCarrierCopiesRequiredIsFalse = refl
  }
