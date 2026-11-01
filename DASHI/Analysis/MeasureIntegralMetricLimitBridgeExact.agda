module DASHI.Analysis.MeasureIntegralMetricLimitBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.MeasureIntegralLimitKernelBidiExact as MIL
import DASHI.Analysis.MetricConvergenceKernelBidiExact as Metric

------------------------------------------------------------------------
-- BRIDGE: INTEGRAL LIMITS -> METRIC / EPSILON LIMITS
--
-- This does not prove convergence.  It says how a measure/integral problem may
-- choose a concrete metric semantics for its parameterised cutoff limit.
------------------------------------------------------------------------

record MeasureIntegralMetricAdapter
    (P : MIL.MeasureIntegralProblem) : Set₁ where
  field
    Epsilon : Set
    Positive : Epsilon → Set
    _≼_ : MIL.Regulator P → MIL.Regulator P → Set
    Close : MIL.Scalar P → MIL.Scalar P → Epsilon → Set

    metricProblem : Metric.ParameterisedMetricLimitProblem

    parameterCarrierWeld : Metric.Parameter metricProblem ≡ MIL.Parameter P
    indexCarrierWeld : Metric.Index metricProblem ≡ MIL.Regulator P
    valueCarrierWeld : Metric.Value metricProblem ≡ MIL.Scalar P
    epsilonCarrierWeld : Metric.Epsilon metricProblem ≡ Epsilon

    familySameObject : Set
    candidateSameObject : Set

    adapterReading : String

open MeasureIntegralMetricAdapter public

record MeasureIntegralMetricCompletion
    (P : MIL.MeasureIntegralProblem)
    (adapter : MeasureIntegralMetricAdapter P) : Set₁ where
  field
    metricConvergence : Metric.PointwiseMetricConvergence (metricProblem adapter)
    integralLimitSameObject : Set
    completionReading : String

open MeasureIntegralMetricCompletion public

record MeasureIntegralMetricObligations
    (P : MIL.MeasureIntegralProblem)
    (adapter : MeasureIntegralMetricAdapter P) : Set₁ where
  field
    regulatorDirectedness : Set
    scalarDistanceSemantics : Set
    epsilonPositivitySemantics : Set
    tailEstimateForIntegratedDifference : Set
    candidateWeldToLimitIntegral : Set
    obligationReading : String

open MeasureIntegralMetricObligations public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MeasureIntegralInterfaceImpliesMetricLimit : Set where

data MetricLimitImpliesIntegralExchange : Set where

measureIntegralInterfaceDoesNotAutoSupplyMetricLimit :
  MeasureIntegralInterfaceImpliesMetricLimit → ⊥
measureIntegralInterfaceDoesNotAutoSupplyMetricLimit ()

metricLimitDoesNotAutoSupplyIntegralExchange :
  MetricLimitImpliesIntegralExchange → ⊥
metricLimitDoesNotAutoSupplyIntegralExchange ()
