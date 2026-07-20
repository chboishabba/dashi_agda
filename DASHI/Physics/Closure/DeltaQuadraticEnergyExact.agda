module DASHI.Physics.Closure.DeltaQuadraticEnergyExact where

open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Integer using (ℤ; +_)
open import Data.Vec using (Vec)

import DASHI.Arithmetic.ArithmeticIntegerEmbedding as AIE
import DASHI.Arithmetic.WeightedValuationEnergy as WVE
open import DASHI.Geometry.ProjectionDefect as PD
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.QuadraticPolarization as QP
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
open import DASHI.Physics.Closure.PrimeWeightedQuadraticForm as PWQ

------------------------------------------------------------------------
-- Exact Delta-side quadratic energy.
--
-- The arithmetic valuation profile is an amplitude vector. Its exact
-- unweighted quadratic energy is therefore the already-canonical
-- sum-of-squares form evaluated on that vector. This deliberately does not
-- identify the older linear cancellation pressure with a quadratic energy.

DeltaCarrier : Set
DeltaCarrier = AIE.Int

DeltaAmplitude : DeltaCarrier → Vec ℤ 15
DeltaAmplitude = WVE.valuationVecℤ

QDelta : DeltaCarrier → ℤ
QDelta n = QP.Q̂core (DeltaAmplitude n)

QDeltaFormCorrect :
  ∀ n →
  QDelta n ≡ QP.Q̂core (WVE.valuationVecℤ n)
QDeltaFormCorrect n = refl

record ExactDeltaQuadraticEnergySurface : Set₁ where
  field
    Carrier : Set
    amplitude : Carrier → Vec ℤ 15
    energy : Carrier → ℤ
    energyIsCanonicalQuadratic :
      ∀ x → energy x ≡ QP.Q̂core (amplitude x)

open ExactDeltaQuadraticEnergySurface public

canonicalExactDeltaQuadraticEnergySurface :
  ExactDeltaQuadraticEnergySurface
canonicalExactDeltaQuadraticEnergySurface =
  record
    { Carrier = DeltaCarrier
    ; amplitude = DeltaAmplitude
    ; energy = QDelta
    ; energyIsCanonicalQuadratic = QDeltaFormCorrect
    }

------------------------------------------------------------------------
-- Reduction to the existing admissibility/normalization theorem.

exactDeltaAgreesWithAdmissibleQuadratic :
  (dynamicsMap :
    PD.Additive.Carrier (QES.AdditiveVecℤ {15}) →
    PD.Additive.Carrier (QES.AdditiveVecℤ {15})) →
  (candidateQuadratic :
    QF.QuadraticForm (QES.AdditiveVecℤ {15}) QES.ScalarFieldℤ) →
  CFQS.AdmissibleFor 15 dynamicsMap candidateQuadratic →
  ∀ n →
    QDelta n
    ≡
    QF.QuadraticForm.Q candidateQuadratic (DeltaAmplitude n)
exactDeltaAgreesWithAdmissibleQuadratic dynamicsMap candidateQuadratic admissible n =
  sym
    (CFQS.admissibleForNormalization admissible (DeltaAmplitude n))

exactDeltaDeterminesAdmissibleQuadraticsOnImage :
  (dynamicsMap :
    PD.Additive.Carrier (QES.AdditiveVecℤ {15}) →
    PD.Additive.Carrier (QES.AdditiveVecℤ {15})) →
  (q₁ q₂ :
    QF.QuadraticForm (QES.AdditiveVecℤ {15}) QES.ScalarFieldℤ) →
  CFQS.AdmissibleFor 15 dynamicsMap q₁ →
  CFQS.AdmissibleFor 15 dynamicsMap q₂ →
  ∀ n →
    QF.QuadraticForm.Q q₁ (DeltaAmplitude n)
    ≡
    QF.QuadraticForm.Q q₂ (DeltaAmplitude n)
exactDeltaDeterminesAdmissibleQuadraticsOnImage dynamicsMap q₁ q₂ admissible₁ admissible₂ n =
  trans
    (CFQS.admissibleForNormalization admissible₁ (DeltaAmplitude n))
    (sym
      (CFQS.admissibleForNormalization admissible₂ (DeltaAmplitude n)))

------------------------------------------------------------------------
-- Exact tracked-prime weighted quadratic geometry.
--
-- The earlier boundary is now sharpened constructively. The finite exact
-- tracked-prime weighting is represented by the genuine diagonal form
--
--   Q_p(v) = Σ_i p_i v_i²
--
-- on Vec ℤ 15. This avoids the incorrect operation of squaring coordinates
-- that have already been multiplied by p_i. A logarithmic weighting remains a
-- later scalar-extension refinement because log p_i is not an integer scalar.

QDeltaWeighted : DeltaCarrier → ℤ
QDeltaWeighted n =
  QF.QuadraticForm.Q PWQ.primeWeightedQuadraticForm (DeltaAmplitude n)

QDeltaWeightedFormCorrect :
  ∀ n →
    QDeltaWeighted n
    ≡
    PWQ.weightedQ PWQ.primeWeightsℤ (WVE.valuationVecℤ n)
QDeltaWeightedFormCorrect n = refl

QDeltaWeightedMatchesArithmeticEnergy :
  ∀ n →
    QDeltaWeighted n ≡ + (WVE.weightedQuadraticEnergy n)
QDeltaWeightedMatchesArithmeticEnergy n = refl

record WeightedDeltaQuadraticSurface : Set₁ where
  field
    Carrier : Set
    amplitude : Carrier → Vec ℤ 15
    weightedForm :
      QF.QuadraticForm (QES.AdditiveVecℤ {15}) QES.ScalarFieldℤ
    weightedEnergy : Carrier → ℤ
    weightedEnergyIsFormEvaluation :
      ∀ x →
      weightedEnergy x
      ≡
      QF.QuadraticForm.Q weightedForm (amplitude x)
    weightedEnergyMatchesArithmetic :
      ∀ x →
      weightedEnergy x ≡ + (WVE.weightedQuadraticEnergy x)

open WeightedDeltaQuadraticSurface public

canonicalWeightedDeltaQuadraticSurface :
  WeightedDeltaQuadraticSurface
canonicalWeightedDeltaQuadraticSurface =
  record
    { Carrier = DeltaCarrier
    ; amplitude = DeltaAmplitude
    ; weightedForm = PWQ.primeWeightedQuadraticForm
    ; weightedEnergy = QDeltaWeighted
    ; weightedEnergyIsFormEvaluation = λ _ → refl
    ; weightedEnergyMatchesArithmetic = QDeltaWeightedMatchesArithmeticEnergy
    }

------------------------------------------------------------------------
-- Honest normalization boundary.
--
-- The weighted form is a real quadratic form, but it is not silently equal to
-- the unweighted Q-hat-core. A weighted-to-canonical promotion must inhabit
-- the existing `AdmissibleFor` normalization seam explicitly.

record WeightedToCanonicalBoundary : Set₁ where
  field
    dynamicsMap :
      PD.Additive.Carrier (QES.AdditiveVecℤ {15}) →
      PD.Additive.Carrier (QES.AdditiveVecℤ {15})
    weightedAdmissible :
      CFQS.AdmissibleFor 15 dynamicsMap PWQ.primeWeightedQuadraticForm

  weightedNormalizesToQ̂core :
    ∀ x →
    QF.QuadraticForm.Q PWQ.primeWeightedQuadraticForm x
    ≡ QP.Q̂core x
  weightedNormalizesToQ̂core =
    CFQS.admissibleForNormalization weightedAdmissible
