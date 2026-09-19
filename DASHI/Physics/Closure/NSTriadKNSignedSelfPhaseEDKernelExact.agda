module DASHI.Physics.Closure.NSTriadKNSignedSelfPhaseEDKernelExact where

------------------------------------------------------------------------
-- SIGN-ROBUST SELF-PHASE ENERGY-DISSIPATION KERNEL
--
-- Round110's original scalar helper assumes the signed Waleffe gap is
-- nonnegative.  That is stronger than the upper-bound argument needs.
--
-- For square mass M >= 0, energies E_p,E_q >= 0, and frequency squares
-- w_p^2,w_q^2 >= 0, it is enough to know
--
--   delta <= w_p^2 + w_q^2
--   M <= E_p E_q.
--
-- Then, regardless of the sign of delta,
--
--   delta M
--     <= (w_p^2 E_p) E_q + E_p (w_q^2 E_q).
--
-- Negative delta is automatically favourable.  No positive-part replacement,
-- absolute value, phase selection, or sign assumption is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

productNonnegative :
  ∀ {a b : ℚ} →
  0ℚ ≤ a →
  0ℚ ≤ b →
  0ℚ ≤ a * b
productNonnegative {a} {b} aNN bNN =
  let
    instance
      aNNI = nonNegative aNN
      bNNI = nonNegative bNN
  in
  ℚP.nonNegative⁻¹ (a * b)

signedSelfPhaseBelowEDKernel :
  (delta omegaP2 omegaQ2 energyP energyQ squareMass : ℚ) →
  0ℚ ≤ omegaP2 →
  0ℚ ≤ omegaQ2 →
  0ℚ ≤ energyP →
  0ℚ ≤ energyQ →
  0ℚ ≤ squareMass →
  delta ≤ omegaP2 + omegaQ2 →
  squareMass ≤ energyP * energyQ →
  delta * squareMass
  ≤ (omegaP2 * energyP) * energyQ
      + energyP * (omegaQ2 * energyQ)
signedSelfPhaseBelowEDKernel
    delta omegaP2 omegaQ2 energyP energyQ squareMass
    omegaPNN omegaQNN energyPNN energyQNN squareNN
    deltaBound squareBound =
  let
    omegaSumNN : 0ℚ ≤ omegaP2 + omegaQ2
    omegaSumNN = ℚP.+-mono-≤ omegaPNN omegaQNN

    energyProductNN : 0ℚ ≤ energyP * energyQ
    energyProductNN = productNonnegative energyPNN energyQNN

    signedToPositiveEnvelope :
      delta * squareMass
      ≤ (omegaP2 + omegaQ2) * squareMass
    signedToPositiveEnvelope =
      let instance squareNNI = nonNegative squareNN
      in ℚP.*-monoʳ-≤-nonNeg squareMass deltaBound

    massToEnergyProduct :
      (omegaP2 + omegaQ2) * squareMass
      ≤ (omegaP2 + omegaQ2) * (energyP * energyQ)
    massToEnergyProduct =
      let instance omegaSumNNI = nonNegative omegaSumNN
      in ℚP.*-monoˡ-≤-nonNeg (omegaP2 + omegaQ2) squareBound

    endpoint :
      (omegaP2 + omegaQ2) * (energyP * energyQ)
      ≡ (omegaP2 * energyP) * energyQ
          + energyP * (omegaQ2 * energyQ)
    endpoint = solve
      (omegaP2 ∷ omegaQ2 ∷ energyP ∷ energyQ ∷ [])
  in
  ℚP.≤-trans signedToPositiveEnvelope
    (ℚP.≤-trans massToEnergyProduct
      (subst
        (λ upper →
          (omegaP2 + omegaQ2) * (energyP * energyQ) ≤ upper)
        endpoint ℚP.≤-refl))

roundSignedSelfPhaseGapNeedNotBeNonnegative : Bool
roundSignedSelfPhaseGapNeedNotBeNonnegative = true

roundSignedSelfPhasePositivePartRequired : Bool
roundSignedSelfPhasePositivePartRequired = false

roundSignedSelfPhaseAbsoluteValueRequired : Bool
roundSignedSelfPhaseAbsoluteValueRequired = false

roundSignedSelfPhaseGapNeedNotBeNonnegativeIsTrue :
  roundSignedSelfPhaseGapNeedNotBeNonnegative ≡ true
roundSignedSelfPhaseGapNeedNotBeNonnegativeIsTrue = refl

roundSignedSelfPhasePositivePartRequiredIsFalse :
  roundSignedSelfPhasePositivePartRequired ≡ false
roundSignedSelfPhasePositivePartRequiredIsFalse = refl

roundSignedSelfPhaseAbsoluteValueRequiredIsFalse :
  roundSignedSelfPhaseAbsoluteValueRequired ≡ false
roundSignedSelfPhaseAbsoluteValueRequiredIsFalse = refl
