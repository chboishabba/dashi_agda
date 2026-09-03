module DASHI.Physics.QuantumVacuum.ParallelPlateRenormalisedDifferenceHighestAlphaExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.PoissonSummationKernelBidiExact as PS
import DASHI.Analysis.RenormalisedDifferenceLimitExact as RDL
import DASHI.Analysis.SumIntegralDefectExact as SID
import DASHI.Analysis.MeasureIntegralLimitKernelBidiExact as MIL
import DASHI.Analysis.MeasureIntegralMetricLimitBridgeExact as MIM
import DASHI.Analysis.MetricConvergenceKernelBidiExact as Metric
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.PerfectConductorMaxwellSpectrumBidiExact as MaxwellSpectrum
import DASHI.Physics.QuantumVacuum.ParallelPlateRegulatedDifferenceBidiExact as Difference
import DASHI.Physics.QuantumVacuum.ParallelPlateTransverseMeasureLimitBidiExact as Transverse
import DASHI.Physics.QuantumVacuum.ParallelPlateTransverseMetricConvergenceBidiExact as TransverseMetric

------------------------------------------------------------------------
-- HIGHEST-ALPHA CASIMIR RENORMALISED-DIFFERENCE CUTSET
--
-- The remaining spectral evaluation is separated into three theorem classes:
--
--   A. algebraic/summation transformation of the same Casimir defect;
--   B. analytic measure/convergence and regulator-removal control;
--   C. exact evaluation of the surviving finite part to the 720 coefficient.
--
-- B is routed through both the generic MeasureIntegralLimit BIDI kernel and a
-- constructive metric/epsilon convergence kernel.
------------------------------------------------------------------------

record CasimirSpectralInput
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    maxwellProducer : MaxwellSpectrum.PerfectConductorSpectrumProducer kernel
    regulatedDifference : Difference.CasimirRegulatedDifference kernel
    longitudinalDefect : Difference.CasimirLongitudinalDefect kernel

    sameSpectrumObject : Set
    sameSeparationObject : Set
    sameRegulatorObject : Set
    inputReading : String

open CasimirSpectralInput public

record DefectTransformationReceipt
    (kernel : Casimir.CasimirScalarModel)
    (input : CasimirSpectralInput kernel) : Set₁ where
  field
    Method : Set
    method : Method

    transformedDefect : SID.SumIntegralDefect
    sameCasimirDefect : Set

    optionalPoissonProblem : PS.PoissonSummationProblem
    poissonUsed : Bool

    transformationClosed : Set
    transformationReading : String

open DefectTransformationReceipt public

record TransverseContinuumAndLimitReceipt
    (kernel : Casimir.CasimirScalarModel)
    (input : CasimirSpectralInput kernel) : Set₁ where
  field
    measureFamily : Transverse.CasimirTransverseMeasureFamily kernel

    measureFamilyUsesInputDifference :
      Transverse.casimirDifference measureFamily ≡ regulatedDifference input

    analyticCompletion :
      Transverse.CasimirTransverseAnalyticCompletion kernel measureFamily

    metricConvergence :
      TransverseMetric.CasimirTransverseMetricConvergence kernel measureFamily

    genericMeasureProblem : MIL.MeasureIntegralProblem
    genericMeasureProblemIsCasimirInstance :
      genericMeasureProblem ≡
      Transverse.asGenericMeasureIntegralProblem kernel measureFamily

    genericMetricProblem : Metric.ParameterisedMetricLimitProblem
    genericMetricProblemIsCasimirInstance :
      genericMetricProblem ≡
      MIM.metricProblem (TransverseMetric.adapter metricConvergence)

    subtractionBeforeLimit : Set
    presentationIndependentLimit : Set

    genericDifferenceReceipt : RDL.RenormalisedDifferenceReceipt
    sameGenericDifferenceAsCasimir : Set

    limitReading : String

open TransverseContinuumAndLimitReceipt public

record Coefficient720EvaluationReceipt
    (kernel : Casimir.CasimirScalarModel)
    (input : CasimirSpectralInput kernel) : Set₁ where
  field
    finitePartCarrier : Set
    finitePart : finitePartCarrier

    piSquaredFactorProduced : Set
    inverseCubeSeparationProduced : Set
    denominator720Produced : Set

    sameFinitePartAsRegulatedLimit : Set
    sameObservableAsCasimirEnergyPerArea : Set

    evaluationReading : String

open Coefficient720EvaluationReceipt public

record RenormalisedDifferenceCompletion
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    input : CasimirSpectralInput kernel
    transform : DefectTransformationReceipt kernel input
    continuumLimit : TransverseContinuumAndLimitReceipt kernel input
    coefficient : Coefficient720EvaluationReceipt kernel input

    completionReading : String

open RenormalisedDifferenceCompletion public

------------------------------------------------------------------------
-- No-promotion boundaries between the theorem classes.
------------------------------------------------------------------------

data DefectTransformationImpliesConvergencePermission : Set where

data MeasureInterfaceImpliesAnalyticCompletionPermission : Set where

data MetricInterfaceImpliesTailEstimatePermission : Set where

data ConvergenceImpliesCoefficient720Permission : Set where

data Coefficient720ImpliesMaxwellSpectrumPermission : Set where

transformationCannotAutoSupplyConvergence :
  DefectTransformationImpliesConvergencePermission → ⊥
transformationCannotAutoSupplyConvergence ()

measureInterfaceCannotAutoSupplyAnalyticCompletion :
  MeasureInterfaceImpliesAnalyticCompletionPermission → ⊥
measureInterfaceCannotAutoSupplyAnalyticCompletion ()

metricInterfaceCannotAutoSupplyTailEstimate :
  MetricInterfaceImpliesTailEstimatePermission → ⊥
metricInterfaceCannotAutoSupplyTailEstimate ()

convergenceCannotAutoSupply720 :
  ConvergenceImpliesCoefficient720Permission → ⊥
convergenceCannotAutoSupply720 ()

coefficientCannotAutoSupplySpectrum :
  Coefficient720ImpliesMaxwellSpectrumPermission → ⊥
coefficientCannotAutoSupplySpectrum ()

------------------------------------------------------------------------
-- Machine-readable current wall.
------------------------------------------------------------------------

record HighestAlphaStatus : Set where
  field
    genericPoissonShapeOwned : Bool
    genericDifferenceShapeOwned : Bool
    genericDefectShapeOwned : Bool
    genericMeasureIntegralLimitShapeOwned : Bool
    genericMetricConvergenceShapeOwned : Bool
    casimirDifferenceInstanceOwned : Bool
    casimirTransverseMeasureInstanceOwned : Bool
    casimirMetricLimitInstanceOwned : Bool
    perfectConductorSpectrumProducerInterfaceOwned : Bool

    literalMaxwellBoundaryPDEClosed : Bool
    concreteTransverseMeasureClosed : Bool
    transverseIntegrabilityClosed : Bool
    dominationAndInterchangeClosed : Bool
    concreteScalarMetricClosed : Bool
    regulatorTailEstimateClosed : Bool
    completenessClosedIfNeeded : Bool
    finitePart720Closed : Bool

    genericPoissonShapeOwnedIsTrue : genericPoissonShapeOwned ≡ true
    genericDifferenceShapeOwnedIsTrue : genericDifferenceShapeOwned ≡ true
    genericDefectShapeOwnedIsTrue : genericDefectShapeOwned ≡ true
    genericMeasureIntegralLimitShapeOwnedIsTrue :
      genericMeasureIntegralLimitShapeOwned ≡ true
    genericMetricConvergenceShapeOwnedIsTrue :
      genericMetricConvergenceShapeOwned ≡ true
    casimirDifferenceInstanceOwnedIsTrue : casimirDifferenceInstanceOwned ≡ true
    casimirTransverseMeasureInstanceOwnedIsTrue :
      casimirTransverseMeasureInstanceOwned ≡ true
    casimirMetricLimitInstanceOwnedIsTrue : casimirMetricLimitInstanceOwned ≡ true
    perfectConductorSpectrumProducerInterfaceOwnedIsTrue :
      perfectConductorSpectrumProducerInterfaceOwned ≡ true

    literalMaxwellBoundaryPDEClosedIsFalse : literalMaxwellBoundaryPDEClosed ≡ false
    concreteTransverseMeasureClosedIsFalse : concreteTransverseMeasureClosed ≡ false
    transverseIntegrabilityClosedIsFalse : transverseIntegrabilityClosed ≡ false
    dominationAndInterchangeClosedIsFalse : dominationAndInterchangeClosed ≡ false
    concreteScalarMetricClosedIsFalse : concreteScalarMetricClosed ≡ false
    regulatorTailEstimateClosedIsFalse : regulatorTailEstimateClosed ≡ false
    completenessClosedIfNeededIsFalse : completenessClosedIfNeeded ≡ false
    finitePart720ClosedIsFalse : finitePart720Closed ≡ false

open HighestAlphaStatus public

canonicalHighestAlphaStatus : HighestAlphaStatus
canonicalHighestAlphaStatus = record
  { genericPoissonShapeOwned = true
  ; genericDifferenceShapeOwned = true
  ; genericDefectShapeOwned = true
  ; genericMeasureIntegralLimitShapeOwned = true
  ; genericMetricConvergenceShapeOwned = true
  ; casimirDifferenceInstanceOwned = true
  ; casimirTransverseMeasureInstanceOwned = true
  ; casimirMetricLimitInstanceOwned = true
  ; perfectConductorSpectrumProducerInterfaceOwned = true
  ; literalMaxwellBoundaryPDEClosed = false
  ; concreteTransverseMeasureClosed = false
  ; transverseIntegrabilityClosed = false
  ; dominationAndInterchangeClosed = false
  ; concreteScalarMetricClosed = false
  ; regulatorTailEstimateClosed = false
  ; completenessClosedIfNeeded = false
  ; finitePart720Closed = false
  ; genericPoissonShapeOwnedIsTrue = refl
  ; genericDifferenceShapeOwnedIsTrue = refl
  ; genericDefectShapeOwnedIsTrue = refl
  ; genericMeasureIntegralLimitShapeOwnedIsTrue = refl
  ; genericMetricConvergenceShapeOwnedIsTrue = refl
  ; casimirDifferenceInstanceOwnedIsTrue = refl
  ; casimirTransverseMeasureInstanceOwnedIsTrue = refl
  ; casimirMetricLimitInstanceOwnedIsTrue = refl
  ; perfectConductorSpectrumProducerInterfaceOwnedIsTrue = refl
  ; literalMaxwellBoundaryPDEClosedIsFalse = refl
  ; concreteTransverseMeasureClosedIsFalse = refl
  ; transverseIntegrabilityClosedIsFalse = refl
  ; dominationAndInterchangeClosedIsFalse = refl
  ; concreteScalarMetricClosedIsFalse = refl
  ; regulatorTailEstimateClosedIsFalse = refl
  ; completenessClosedIfNeededIsFalse = refl
  ; finitePart720ClosedIsFalse = refl
  }
