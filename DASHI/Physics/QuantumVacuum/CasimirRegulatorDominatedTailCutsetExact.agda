module DASHI.Physics.QuantumVacuum.CasimirRegulatorDominatedTailCutsetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.MeasureIntegralLimitKernelBidiExact as MIL
import DASHI.Analysis.MetricConvergenceKernelBidiExact as Metric
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.ParallelPlateTransverseMeasureLimitBidiExact as Transverse

------------------------------------------------------------------------
-- REGULATOR DOMINATION / INTERCHANGE / EPSILON-TAIL CUTSET
------------------------------------------------------------------------

record RegulatedDifferenceDominatingFamily
    (kernel : Casimir.CasimirScalarModel)
    (F : Transverse.CasimirTransverseMeasureFamily kernel) : Set₁ where
  field
    Dominator : Set
    dominator : Dominator

    dominatesEveryCutoff : Set
    dominatorIntegrable : Set
    dominationUniformInLongitudinalIndex : Set
    dominationPreservedAfterSubtraction : Set
    reading : String

open RegulatedDifferenceDominatingFamily public

record SumIntegralExchangeProducer
    (kernel : Casimir.CasimirScalarModel)
    (F : Transverse.CasimirTransverseMeasureFamily kernel) : Set₁ where
  field
    interchangeProblem : Transverse.CasimirSumIntegralInterchange kernel F
    genericReceipt :
      MIL.OperationInterchangeReceipt
        (Transverse.asGenericInterchangeProblem kernel F interchangeProblem)

    absoluteOrDominatedSummability : Set
    sameRegulatedIntegrand : Set
    reading : String

open SumIntegralExchangeProducer public

record LimitIntegralExchangeProducer
    (kernel : Casimir.CasimirScalarModel)
    (F : Transverse.CasimirTransverseMeasureFamily kernel) : Set₁ where
  field
    genericProblem : MIL.MeasureIntegralProblem
    sameProblemAsCasimir :
      genericProblem ≡ Transverse.asGenericMeasureIntegralProblem kernel F

    completion : MIL.MeasureIntegralLimitCompletion genericProblem
    subtractionPerformedBeforeLimit : Set
    sameCandidateLimit : Set
    reading : String

open LimitIntegralExchangeProducer public

record RegulatorTailEstimate : Set₁ where
  field
    Parameter Index Value Epsilon : Set
    metricProblem : Metric.ParameterisedMetricLimitProblem

    thresholdFormula : Parameter → Epsilon → Index
    tailEstimate : Set
    presentationIndependentTail : Set
    reading : String

open RegulatorTailEstimate public

record CasimirRegulatorAnalyticCompletion
    (kernel : Casimir.CasimirScalarModel)
    (F : Transverse.CasimirTransverseMeasureFamily kernel) : Set₁ where
  field
    dominator : RegulatedDifferenceDominatingFamily kernel F
    sumIntegral : SumIntegralExchangeProducer kernel F
    limitIntegral : LimitIntegralExchangeProducer kernel F
    regulatorTail : RegulatorTailEstimate

    sameObjectAcrossAllFourStages : Set
    regulatorRemovalClosed : Set
    presentationIndependenceClosed : Set
    reading : String

open CasimirRegulatorAnalyticCompletion public

data DominatorAutomaticallySuppliesExchange : Set where
data PointwiseLimitAutomaticallySuppliesIntegratedLimit : Set where

dominatorNeedsExchangeTheorem : DominatorAutomaticallySuppliesExchange → ⊥
dominatorNeedsExchangeTheorem ()

pointwiseLimitNeedsIntegralTheorem :
  PointwiseLimitAutomaticallySuppliesIntegratedLimit → ⊥
pointwiseLimitNeedsIntegralTheorem ()
