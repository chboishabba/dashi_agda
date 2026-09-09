module DASHI.Biology.CausalEstimatorMetricConsistencyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Analysis.MetricConvergenceKernelBidiExact as Metric
import DASHI.Biology.CausalEffectEstimandExact as Estimand
import DASHI.Biology.CausalEstimandStatisticalRealisationExact as Statistical
import DASHI.Biology.CausalEstimatorGuaranteesExact as Guarantees

------------------------------------------------------------------------
-- METRIC CONSISTENCY REALISATION FOR CAUSAL ESTIMATORS
--
-- The repository already owns a generic epsilon/tail metric-convergence kernel.
-- This module does not invent convergence in probability or asymptotic measure
-- theory.  It realises estimator consistency as ordinary pointwise metric
-- convergence of an indexed estimator family to the exact selected target.
------------------------------------------------------------------------

data SingleEstimandParameter : Set where
  selectedEstimand : SingleEstimandParameter

record EstimatorMetricConsistencySurface
    {estimand : Estimand.CausalEffectEstimand}
    (procedure : Statistical.EstimatorProcedure estimand) : Set₁ where
  constructor estimator-metric-consistency-surface
  field
    Index Value Epsilon : Set

    _≼_ : Index → Index → Set
    Positive : Epsilon → Set
    Close : Value → Value → Epsilon → Set

    sampleAt : Index → Statistical.Sample procedure
    estimateToValue : Statistical.Estimate procedure → Value
    targetValue : Value

    indexReference : String
    metricReference : String
    targetReference : String
    samplingFamilyReference : String

open EstimatorMetricConsistencySurface public

asMetricLimitProblem :
  ∀ {estimand}
    {procedure : Statistical.EstimatorProcedure estimand} →
  EstimatorMetricConsistencySurface procedure →
  Metric.ParameterisedMetricLimitProblem
asMetricLimitProblem {procedure = procedure} surface = record
  { Parameter = SingleEstimandParameter
  ; Index = Index surface
  ; Value = Value surface
  ; Epsilon = Epsilon surface
  ; _≼_ = _≼_ surface
  ; Positive = Positive surface
  ; Close = Close surface
  ; family = λ _ index →
      estimateToValue surface
        (Statistical.estimator procedure (sampleAt surface index))
  ; candidate = λ _ → targetValue surface
  ; reading =
      "Indexed estimator outputs converge in an application-supplied metric to the exact selected estimand target."
  }

record MetricConsistencyGuarantee
    {estimand : Estimand.CausalEffectEstimand}
    (procedure : Statistical.EstimatorProcedure estimand)
    (surface : EstimatorMetricConsistencySurface procedure) : Set₁ where
  constructor metric-consistency-guarantee
  field
    convergence :
      Metric.PointwiseMetricConvergence (asMetricLimitProblem surface)

    targetIsSameEstimand : Set
    targetSameObjectReceipt : targetIsSameEstimand

    consistencyReference : String
    targetWeldReference : String

open MetricConsistencyGuarantee public

metricConsistencyTail :
  ∀ {estimand procedure surface}
    (guarantee : MetricConsistencyGuarantee
      {estimand} procedure surface) →
  (ε : Epsilon surface) →
  Positive surface ε →
  (index : Index surface) →
  _≼_ surface
    (Metric.threshold (convergence guarantee) selectedEstimand ε)
    index →
  Close surface
    (estimateToValue surface
      (Statistical.estimator procedure (sampleAt surface index)))
    (targetValue surface)
    ε
metricConsistencyTail guarantee ε positive index afterThreshold =
  Metric.tailClose
    (convergence guarantee)
    selectedEstimand
    ε
    positive
    index
    afterThreshold

------------------------------------------------------------------------
-- Compatibility adapter into the earlier generic guarantee carrier.
------------------------------------------------------------------------

asGenericConsistencyGuarantee :
  ∀ {estimand procedure surface} →
  MetricConsistencyGuarantee {estimand} procedure surface →
  Guarantees.ConsistencyGuarantee procedure
asGenericConsistencyGuarantee {surface = surface} guarantee = record
  { Index = SingleEstimandParameter
  ; ConsistencyProperty = λ _ →
      Metric.PointwiseMetricConvergence
        (asMetricLimitProblem surface)
  ; consistencyReceipt = λ _ → convergence guarantee
  ; limitOrRefinementReference =
      "DASHI.Analysis.MetricConvergenceKernelBidiExact.PointwiseMetricConvergence"
  ; consistencyReference = consistencyReference guarantee
  }

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MetricConsistencyMeansConvergenceInProbabilityPermission : Set where

data MetricConsistencyMeansAsymptoticNormalityPermission : Set where

data PointwiseMeansUniformConsistencyPermission : Set where

data CauchyMeansConsistentWithoutLimitPermission : Set where

data ConsistencyMeansUnbiasedPermission : Set where

data ConsistencyMeansCausalIdentificationPermission : Set where

data MetricConsistencyMeansRepresentativeSamplingPermission : Set where

metricConsistencyDoesNotInventConvergenceInProbability :
  MetricConsistencyMeansConvergenceInProbabilityPermission → ⊥
metricConsistencyDoesNotInventConvergenceInProbability ()

metricConsistencyDoesNotInventAsymptoticNormality :
  MetricConsistencyMeansAsymptoticNormalityPermission → ⊥
metricConsistencyDoesNotInventAsymptoticNormality ()

pointwiseConsistencyDoesNotBecomeUniformConsistency :
  PointwiseMeansUniformConsistencyPermission → ⊥
pointwiseConsistencyDoesNotBecomeUniformConsistency ()

cauchyReceiptDoesNotSupplySelectedTargetLimit :
  CauchyMeansConsistentWithoutLimitPermission → ⊥
cauchyReceiptDoesNotSupplySelectedTargetLimit ()

consistencyDoesNotBecomeUnbiasedness :
  ConsistencyMeansUnbiasedPermission → ⊥
consistencyDoesNotBecomeUnbiasedness ()

consistencyDoesNotIdentifyCause :
  ConsistencyMeansCausalIdentificationPermission → ⊥
consistencyDoesNotIdentifyCause ()

metricConsistencyDoesNotProveRepresentativeSampling :
  MetricConsistencyMeansRepresentativeSamplingPermission → ⊥
metricConsistencyDoesNotProveRepresentativeSampling ()

record CausalEstimatorMetricConsistencyBoundary : Set where
  constructor causal-estimator-metric-consistency-boundary
  field
    genericMetricConvergenceKernelReused : Bool
    indexedEstimatorFamilyExplicit : Bool
    exactTargetSameObjectReceiptRequired : Bool
    pointwiseMetricConsistencyAvailable : Bool
    convergenceInProbabilityInventedHere : Bool
    asymptoticNormalityInventedHere : Bool
    uniformConsistencyAutomatic : Bool
    causalIdentificationAutomatic : Bool

canonicalCausalEstimatorMetricConsistencyBoundary :
  CausalEstimatorMetricConsistencyBoundary
canonicalCausalEstimatorMetricConsistencyBoundary =
  causal-estimator-metric-consistency-boundary
    true true true true false false false false
