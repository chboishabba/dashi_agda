module DASHI.Physics.QuantumVacuum.ParallelPlateTransverseMetricConvergenceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.MeasureIntegralMetricLimitBridgeExact as MIM
import DASHI.Analysis.MetricConvergenceKernelBidiExact as Metric
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.ParallelPlateTransverseMeasureLimitBidiExact as Transverse

------------------------------------------------------------------------
-- CASIMIR TRANSVERSE METRIC CONVERGENCE, BIDI
--
-- This binds the Casimir transverse integral family to the generic epsilon/tail
-- convergence kernel.  The remaining payment is concrete scalar/metric/order
-- semantics plus an actual tail estimate.
------------------------------------------------------------------------

record CasimirTransverseMetricConvergence
    (kernel : Casimir.CasimirScalarModel)
    (F : Transverse.CasimirTransverseMeasureFamily kernel) : Set₁ where
  field
    adapter :
      MIM.MeasureIntegralMetricAdapter
        (Transverse.asGenericMeasureIntegralProblem kernel F)

    completion :
      MIM.MeasureIntegralMetricCompletion
        (Transverse.asGenericMeasureIntegralProblem kernel F)
        adapter

    sameCasimirRegulatedDifference : Set
    sameRenormalisedCandidate : Set
    convergenceReading : String

open CasimirTransverseMetricConvergence public

record CasimirMetricConvergenceObligations
    (kernel : Casimir.CasimirScalarModel)
    (F : Transverse.CasimirTransverseMeasureFamily kernel) : Set₁ where
  field
    ScalarMetric : Set
    Epsilon : Set
    CutoffOrder : Set

    scalarMetricSemantics : ScalarMetric
    epsilonSemantics : Epsilon
    cutoffOrderSemantics : CutoffOrder

    cutoffDirected : Set
    tailEstimateForTransverseIntegralDifference : Set
    candidateIsRenormalisedCasimirObservable : Set
    parameterDependenceControlled : Set

    obligationReading : String

open CasimirMetricConvergenceObligations public

------------------------------------------------------------------------
-- A Cauchy route is allowed, but completeness remains separate.
------------------------------------------------------------------------

record CasimirCauchyRoute
    (kernel : Casimir.CasimirScalarModel)
    (F : Transverse.CasimirTransverseMeasureFamily kernel)
    (adapter :
      MIM.MeasureIntegralMetricAdapter
        (Transverse.asGenericMeasureIntegralProblem kernel F)) : Set₁ where
  field
    cauchy : Metric.MetricCauchyReceipt (MIM.metricProblem adapter)
    completeness : Metric.CompletenessBridge (MIM.metricProblem adapter) cauchy
    sameCandidateAsCasimirLimit : Set
    routeReading : String

open CasimirCauchyRoute public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RationalAlgebraAutomaticallySuppliesRealCompleteness : Set where

data CauchyWithoutCompletenessClosesCasimirLimit : Set where

rationalAlgebraDoesNotAutoSupplyRealCompleteness :
  RationalAlgebraAutomaticallySuppliesRealCompleteness → ⊥
rationalAlgebraDoesNotAutoSupplyRealCompleteness ()

cauchyWithoutCompletenessCannotCloseCasimirLimit :
  CauchyWithoutCompletenessClosesCasimirLimit → ⊥
cauchyWithoutCompletenessCannotCloseCasimirLimit ()

record CasimirMetricLimitStatus : Set where
  field
    genericMetricConvergenceKernelOwned : Bool
    measureToMetricBridgeOwned : Bool
    casimirMetricInstanceInterfaceOwned : Bool
    concreteScalarMetricClosed : Bool
    tailEstimateClosed : Bool
    completenessClosedIfNeeded : Bool

    genericMetricConvergenceKernelOwnedIsTrue : genericMetricConvergenceKernelOwned ≡ true
    measureToMetricBridgeOwnedIsTrue : measureToMetricBridgeOwned ≡ true
    casimirMetricInstanceInterfaceOwnedIsTrue : casimirMetricInstanceInterfaceOwned ≡ true
    concreteScalarMetricClosedIsFalse : concreteScalarMetricClosed ≡ false
    tailEstimateClosedIsFalse : tailEstimateClosed ≡ false
    completenessClosedIfNeededIsFalse : completenessClosedIfNeeded ≡ false

open CasimirMetricLimitStatus public

canonicalCasimirMetricLimitStatus : CasimirMetricLimitStatus
canonicalCasimirMetricLimitStatus = record
  { genericMetricConvergenceKernelOwned = true
  ; measureToMetricBridgeOwned = true
  ; casimirMetricInstanceInterfaceOwned = true
  ; concreteScalarMetricClosed = false
  ; tailEstimateClosed = false
  ; completenessClosedIfNeeded = false
  ; genericMetricConvergenceKernelOwnedIsTrue = refl
  ; measureToMetricBridgeOwnedIsTrue = refl
  ; casimirMetricInstanceInterfaceOwnedIsTrue = refl
  ; concreteScalarMetricClosedIsFalse = refl
  ; tailEstimateClosedIsFalse = refl
  ; completenessClosedIfNeededIsFalse = refl
  }
