module DASHI.Physics.QuantumVacuum.ParallelPlateRenormalisedDifferenceHighestAlphaExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.PoissonSummationKernelBidiExact as PS
import DASHI.Analysis.RenormalisedDifferenceLimitExact as RDL
import DASHI.Analysis.SumIntegralDefectExact as SID
import DASHI.Analysis.MeasureIntegralLimitKernelBidiExact as MIL
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.PerfectConductorMaxwellSpectrumBidiExact as MaxwellSpectrum
import DASHI.Physics.QuantumVacuum.ParallelPlateRegulatedDifferenceBidiExact as Difference
import DASHI.Physics.QuantumVacuum.ParallelPlateTransverseMeasureLimitBidiExact as Transverse

------------------------------------------------------------------------
-- HIGHEST-ALPHA CASIMIR RENORMALISED-DIFFERENCE CUTSET
--
-- The remaining spectral evaluation is separated into three theorem classes:
--
--   A. algebraic/summation transformation of the same Casimir defect;
--   B. analytic measure/convergence and regulator-removal control;
--   C. exact evaluation of the surviving finite part to the 720 coefficient.
--
-- B is no longer an opaque Set-valued socket: it is routed through the generic
-- MeasureIntegralLimit BIDI kernel, with a Casimir-native transverse instance.
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

    genericMeasureProblem : MIL.MeasureIntegralProblem
    genericMeasureProblemIsCasimirInstance :
      genericMeasureProblem ≡
      Transverse.asGenericMeasureIntegralProblem kernel measureFamily

    subtractionBeforeLimit : Set
    regulatorRemovalConverges : Set
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

data ConvergenceImpliesCoefficient720Permission : Set where

data Coefficient720ImpliesMaxwellSpectrumPermission : Set where

transformationCannotAutoSupplyConvergence :
  DefectTransformationImpliesConvergencePermission → ⊥
transformationCannotAutoSupplyConvergence ()

measureInterfaceCannotAutoSupplyAnalyticCompletion :
  MeasureInterfaceImpliesAnalyticCompletionPermission → ⊥
measureInterfaceCannotAutoSupplyAnalyticCompletion ()

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
    casimirDifferenceInstanceOwned : Bool
    casimirTransverseMeasureInstanceOwned : Bool
    perfectConductorSpectrumProducerInterfaceOwned : Bool

    literalMaxwellBoundaryPDEClosed : Bool
    concreteTransverseMeasureClosed : Bool
    transverseIntegrabilityClosed : Bool
    dominationAndLimitExchangeClosed : Bool
    regulatorRemovalClosed : Bool
    finitePart720Closed : Bool

    genericPoissonShapeOwnedIsTrue : genericPoissonShapeOwned ≡ true
    genericDifferenceShapeOwnedIsTrue : genericDifferenceShapeOwned ≡ true
    genericDefectShapeOwnedIsTrue : genericDefectShapeOwned ≡ true
    genericMeasureIntegralLimitShapeOwnedIsTrue :
      genericMeasureIntegralLimitShapeOwned ≡ true
    casimirDifferenceInstanceOwnedIsTrue : casimirDifferenceInstanceOwned ≡ true
    casimirTransverseMeasureInstanceOwnedIsTrue :
      casimirTransverseMeasureInstanceOwned ≡ true
    perfectConductorSpectrumProducerInterfaceOwnedIsTrue :
      perfectConductorSpectrumProducerInterfaceOwned ≡ true

    literalMaxwellBoundaryPDEClosedIsFalse :
      literalMaxwellBoundaryPDEClosed ≡ false
    concreteTransverseMeasureClosedIsFalse :
      concreteTransverseMeasureClosed ≡ false
    transverseIntegrabilityClosedIsFalse :
      transverseIntegrabilityClosed ≡ false
    dominationAndLimitExchangeClosedIsFalse :
      dominationAndLimitExchangeClosed ≡ false
    regulatorRemovalClosedIsFalse : regulatorRemovalClosed ≡ false
    finitePart720ClosedIsFalse : finitePart720Closed ≡ false

open HighestAlphaStatus public

canonicalHighestAlphaStatus : HighestAlphaStatus
canonicalHighestAlphaStatus = record
  { genericPoissonShapeOwned = true
  ; genericDifferenceShapeOwned = true
  ; genericDefectShapeOwned = true
  ; genericMeasureIntegralLimitShapeOwned = true
  ; casimirDifferenceInstanceOwned = true
  ; casimirTransverseMeasureInstanceOwned = true
  ; perfectConductorSpectrumProducerInterfaceOwned = true
  ; literalMaxwellBoundaryPDEClosed = false
  ; concreteTransverseMeasureClosed = false
  ; transverseIntegrabilityClosed = false
  ; dominationAndLimitExchangeClosed = false
  ; regulatorRemovalClosed = false
  ; finitePart720Closed = false
  ; genericPoissonShapeOwnedIsTrue = refl
  ; genericDifferenceShapeOwnedIsTrue = refl
  ; genericDefectShapeOwnedIsTrue = refl
  ; genericMeasureIntegralLimitShapeOwnedIsTrue = refl
  ; casimirDifferenceInstanceOwnedIsTrue = refl
  ; casimirTransverseMeasureInstanceOwnedIsTrue = refl
  ; perfectConductorSpectrumProducerInterfaceOwnedIsTrue = refl
  ; literalMaxwellBoundaryPDEClosedIsFalse = refl
  ; concreteTransverseMeasureClosedIsFalse = refl
  ; transverseIntegrabilityClosedIsFalse = refl
  ; dominationAndLimitExchangeClosedIsFalse = refl
  ; regulatorRemovalClosedIsFalse = refl
  ; finitePart720ClosedIsFalse = refl
  }
