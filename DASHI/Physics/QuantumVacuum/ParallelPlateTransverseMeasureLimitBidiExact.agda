module DASHI.Physics.QuantumVacuum.ParallelPlateTransverseMeasureLimitBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.MeasureIntegralLimitKernelBidiExact as MIL
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.ParallelPlateModeSpectrumCutsetExact as Cutset
import DASHI.Physics.QuantumVacuum.ParallelPlateRegulatedDifferenceBidiExact as Difference

------------------------------------------------------------------------
-- CASIMIR TRANSVERSE MEASURE / LIMIT INSTANCE, BIDI
--
-- This owner instantiates the generic measure/integral/limit theorem shape on
-- the literal regulated Casimir difference.  It does not prove Lebesgue
-- integration or convergence.  Its job is to keep every analytic payment on
-- the same physical object and expose reverse obligations precisely.
------------------------------------------------------------------------

record CasimirTransverseMeasureFamily
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    casimirDifference : Difference.CasimirRegulatedDifference kernel

    TransversePoint : Set
    Measure : Set
    Integrand : Set

    transverseMeasure : Measure

    regulatedIntegrand :
      Cutset.Cutoff (Difference.regulator casimirDifference) →
      TransversePoint → Integrand

    limitIntegrand : TransversePoint → Integrand

    integrate : Measure → (TransversePoint → Integrand) → Casimir.Scalar kernel

    regulatedTransverseIntegral :
      Cutset.Cutoff (Difference.regulator casimirDifference) →
      Casimir.Scalar kernel

    renormalisedTransverseIntegral : Casimir.Scalar kernel

    regulatedIntegralLaw :
      (Λ : Cutset.Cutoff (Difference.regulator casimirDifference)) →
      regulatedTransverseIntegral Λ ≡
      integrate transverseMeasure (regulatedIntegrand Λ)

    renormalisedIntegralLaw :
      renormalisedTransverseIntegral ≡
      integrate transverseMeasure limitIntegrand

    integralIsLiteralRegulatedDifference :
      (Λ : Cutset.Cutoff (Difference.regulator casimirDifference)) →
      regulatedTransverseIntegral Λ ≡
      Difference.regulatedDifference casimirDifference Λ

    familyReading : String

open CasimirTransverseMeasureFamily public

asGenericMeasureIntegralProblem :
  (kernel : Casimir.CasimirScalarModel) →
  CasimirTransverseMeasureFamily kernel →
  MIL.MeasureIntegralProblem
asGenericMeasureIntegralProblem kernel F = record
  { Parameter = ⊤
  ; Regulator = Cutset.Cutoff (Difference.regulator (casimirDifference F))
  ; Point = TransversePoint F
  ; Scalar = Casimir.Scalar kernel
  ; Integrand = Integrand F
  ; Measure = Measure F
  ; measure = transverseMeasure F
  ; regulatedIntegrand = λ _ Λ → regulatedIntegrand F Λ
  ; limitIntegrand = λ _ → limitIntegrand F
  ; integrate = integrate F
  ; regulatedIntegral = λ _ Λ → regulatedTransverseIntegral F Λ
  ; limitIntegral = λ _ → renormalisedTransverseIntegral F
  ; regulatedIntegralLaw = λ _ Λ → regulatedIntegralLaw F Λ
  ; limitIntegralLaw = λ _ → renormalisedIntegralLaw F
  ; reading = "Casimir transverse continuum on the literal regulated plate/reference difference."
  }

------------------------------------------------------------------------
-- Longitudinal-sum / transverse-integral interchange instance.
------------------------------------------------------------------------

record CasimirSumIntegralInterchange
    (kernel : Casimir.CasimirScalarModel)
    (F : CasimirTransverseMeasureFamily kernel) : Set₁ where
  field
    Input : Set
    Intermediate : Set

    longitudinalSumFirst : Input → Intermediate
    transverseIntegralAfterSum : Intermediate → Casimir.Scalar kernel

    transverseIntegralFirst : Input → Intermediate
    longitudinalSumAfterIntegral : Intermediate → Casimir.Scalar kernel

    admissible : Input → Set
    sameCasimirIntegrand : Set
    interchangeReading : String

open CasimirSumIntegralInterchange public

asGenericInterchangeProblem :
  (kernel : Casimir.CasimirScalarModel) →
  (F : CasimirTransverseMeasureFamily kernel) →
  CasimirSumIntegralInterchange kernel F →
  MIL.OperationInterchangeProblem
asGenericInterchangeProblem kernel F I = record
  { Input = Input I
  ; Intermediate = Intermediate I
  ; Output = Casimir.Scalar kernel
  ; leftFirst = longitudinalSumFirst I
  ; rightSecond = transverseIntegralAfterSum I
  ; rightFirst = transverseIntegralFirst I
  ; leftSecond = longitudinalSumAfterIntegral I
  ; admissible = admissible I
  ; reading = "Casimir longitudinal-sum/transverse-integral interchange on one regulated integrand."
  }

------------------------------------------------------------------------
-- Forward analytic completion and reverse consumer obligations.
------------------------------------------------------------------------

record CasimirTransverseAnalyticCompletion
    (kernel : Casimir.CasimirScalarModel)
    (F : CasimirTransverseMeasureFamily kernel) : Set₁ where
  field
    genericCompletion :
      MIL.MeasureIntegralLimitCompletion (asGenericMeasureIntegralProblem kernel F)

    interchangeProblem : CasimirSumIntegralInterchange kernel F
    interchangeReceipt :
      MIL.OperationInterchangeReceipt
        (asGenericInterchangeProblem kernel F interchangeProblem)

    subtractionBeforeLimit : Set
    sameObjectWeldToRegulatedDifference : Set
    presentationIndependentLimit : Set

    completionReading : String

open CasimirTransverseAnalyticCompletion public

record CasimirTransverseAnalyticObligations
    (kernel : Casimir.CasimirScalarModel)
    (F : CasimirTransverseMeasureFamily kernel) : Set₁ where
  field
    transverseMeasureSemantics : Set
    subtractionBeforeIntegration : Set
    regulatedDifferenceIntegrable : Set
    integrableDominatorExists : Set
    dominationUniformInCutoff : Set
    pointwiseCutoffLimit : Set
    longitudinalSumIntegralExchange : Set
    cutoffIntegralLimitExchange : Set
    regulatorRemovalConverges : Set
    resultIndependentOfPresentation : Set
    sameObjectAsCasimirDifference : Set

    obligationReading : String

open CasimirTransverseAnalyticObligations public

------------------------------------------------------------------------
-- Firewalls: a formal continuum representation is not an analytic proof.
------------------------------------------------------------------------

data TransverseIntegralRepresentationImpliesIntegrability : Set where

data SumIntegralRewriteImpliesLimitExchange : Set where

data RegulatedDifferenceImpliesDominatedConvergence : Set where

representationCannotAutoSupplyIntegrability :
  TransverseIntegralRepresentationImpliesIntegrability → ⊥
representationCannotAutoSupplyIntegrability ()

sumIntegralRewriteCannotAutoSupplyLimitExchange :
  SumIntegralRewriteImpliesLimitExchange → ⊥
sumIntegralRewriteCannotAutoSupplyLimitExchange ()

regulatedDifferenceCannotAutoSupplyDominatedConvergence :
  RegulatedDifferenceImpliesDominatedConvergence → ⊥
regulatedDifferenceCannotAutoSupplyDominatedConvergence ()

record CasimirTransverseMeasureStatus : Set where
  field
    genericMeasureLimitKernelOwned : Bool
    casimirMeasureInstanceInterfaceOwned : Bool
    sumIntegralInterchangeInterfaceOwned : Bool
    concreteTransverseMeasureClosed : Bool
    integrabilityClosed : Bool
    dominationClosed : Bool
    cutoffLimitExchangeClosed : Bool

    genericMeasureLimitKernelOwnedIsTrue : genericMeasureLimitKernelOwned ≡ true
    casimirMeasureInstanceInterfaceOwnedIsTrue : casimirMeasureInstanceInterfaceOwned ≡ true
    sumIntegralInterchangeInterfaceOwnedIsTrue : sumIntegralInterchangeInterfaceOwned ≡ true
    concreteTransverseMeasureClosedIsFalse : concreteTransverseMeasureClosed ≡ false
    integrabilityClosedIsFalse : integrabilityClosed ≡ false
    dominationClosedIsFalse : dominationClosed ≡ false
    cutoffLimitExchangeClosedIsFalse : cutoffLimitExchangeClosed ≡ false

open CasimirTransverseMeasureStatus public

canonicalCasimirTransverseMeasureStatus : CasimirTransverseMeasureStatus
canonicalCasimirTransverseMeasureStatus = record
  { genericMeasureLimitKernelOwned = true
  ; casimirMeasureInstanceInterfaceOwned = true
  ; sumIntegralInterchangeInterfaceOwned = true
  ; concreteTransverseMeasureClosed = false
  ; integrabilityClosed = false
  ; dominationClosed = false
  ; cutoffLimitExchangeClosed = false
  ; genericMeasureLimitKernelOwnedIsTrue = refl
  ; casimirMeasureInstanceInterfaceOwnedIsTrue = refl
  ; sumIntegralInterchangeInterfaceOwnedIsTrue = refl
  ; concreteTransverseMeasureClosedIsFalse = refl
  ; integrabilityClosedIsFalse = refl
  ; dominationClosedIsFalse = refl
  ; cutoffLimitExchangeClosedIsFalse = refl
  }
