module DASHI.Physics.Closure.DeltaQuadraticEnergyExact where

open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Integer using (ℤ)
open import Data.Vec using (Vec)

import DASHI.Arithmetic.ArithmeticIntegerEmbedding as AIE
import DASHI.Arithmetic.WeightedValuationEnergy as WVE
open import DASHI.Geometry.ProjectionDefect as PD
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.QuadraticPolarization as QP
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS

------------------------------------------------------------------------
-- Exact Delta-side quadratic energy.
--
-- The arithmetic valuation profile is an amplitude vector.  Its exact
-- quadratic energy is therefore the already-canonical sum-of-squares form
-- evaluated on that vector.  This deliberately does not identify the older
-- linear cancellation pressure with a quadratic energy, and it does not
-- introduce square-root prime weights over the integer carrier.

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
--
-- Once a candidate quadratic is admissible for the theorem-side dynamics,
-- admissibleForNormalization already proves that it is Q-hat-core.  Hence the
-- exact Delta energy agrees with that candidate on every transported
-- valuation amplitude without any new postulate.

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
-- Honest boundary for the weighted route.
--
-- WVE.weightedQuadraticEnergy is retained as a separate arithmetic
-- measurement.  Over the present integer carrier it is not definitionally
-- Q-hat-core of weightedQuadraticVecZ: that latter expression would square the
-- already weighted coordinates again.  Any weighted-to-canonical theorem must
-- therefore provide a genuine weighted quadratic form or a scalar-extension
-- transport, rather than reusing the unweighted normalization by assertion.

record WeightedDeltaQuadraticBoundary : Set₁ where
  field
    weightedArithmeticEnergy : DeltaCarrier → Nat
    weightedArithmeticEnergyIsCurrent :
      weightedArithmeticEnergy ≡ WVE.weightedQuadraticEnergy
    weightedToCanonicalRequiresNewGeometry : Set

canonicalWeightedDeltaQuadraticBoundary : WeightedDeltaQuadraticBoundary
canonicalWeightedDeltaQuadraticBoundary =
  record
    { weightedArithmeticEnergy = WVE.weightedQuadraticEnergy
    ; weightedArithmeticEnergyIsCurrent = refl
    ; weightedToCanonicalRequiresNewGeometry =
        ∀ n →
          ℤ
    }
