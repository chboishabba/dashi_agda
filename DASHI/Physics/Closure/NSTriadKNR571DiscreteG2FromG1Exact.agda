module DASHI.Physics.Closure.NSTriadKNR571DiscreteG2FromG1Exact where

------------------------------------------------------------------------
-- PERIODIC B: DISCRETE G2 FROM G1, NO FREQUENCY DIFFERENTIABILITY
--
-- The R571 second-moment carrier asks only
--
--   |g+ - g-| <= displacement * G2.
--
-- On a nonzero lattice displacement we have displacement >= 1.  Therefore a
-- common amplitude envelope G1 immediately supplies G2 = 2 G1:
--
--   |g+ - g-| <= |g+| + |g-| <= 2 G1 <= displacement * (2 G1).
--
-- This is the correct discrete theorem.  It does not assert differentiability
-- of arbitrary Fourier coefficients with respect to frequency.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_; ∣_∣; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNR571HermitianScalarizedOppositePairExact as G0
import DASHI.Physics.Closure.NSTriadKNR571HermitianStateAmplitudeEnvelopeExact as G1

two : ℚ
two = 1ℚ + 1ℚ

differenceMagnitudeBelowTwoEnvelope :
  (XPlus XMinus D : C3.Complex3 G0.Weld.F) →
  ∣ G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D ∣
  ≤ two * G1.stateAmplitudeEnvelope XPlus XMinus D
differenceMagnitudeBelowTwoEnvelope XPlus XMinus D =
  let
    triangle :
      ∣ G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D ∣
      ≤
      ∣ G0.hermitianScalar XPlus D ∣
      + ∣ G0.hermitianScalar XMinus D ∣
    triangle =
      subst
        (λ rhs →
          ∣ G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D ∣
          ≤ rhs)
        (solve
          ( ∣ G0.hermitianScalar XPlus D ∣
          ∷ ∣ G0.hermitianScalar XMinus D ∣
          ∷ []))
        (ℚP.∣p-q∣≤∣p∣+∣q∣
          (G0.hermitianScalar XPlus D)
          (G0.hermitianScalar XMinus D))

    summed :
      ∣ G0.hermitianScalar XPlus D ∣
      + ∣ G0.hermitianScalar XMinus D ∣
      ≤
      G1.stateAmplitudeEnvelope XPlus XMinus D
      + G1.stateAmplitudeEnvelope XPlus XMinus D
    summed =
      ℚP.+-mono-≤
        (G1.plusHermitianMagnitudeBelowStateEnvelope XPlus XMinus D)
        (G1.minusHermitianMagnitudeBelowStateEnvelope XPlus XMinus D)
  in
  ℚP.≤-trans triangle
    (subst
      ( ( ∣ G0.hermitianScalar XPlus D ∣
        + ∣ G0.hermitianScalar XMinus D ∣) ≤_)
      (solve (G1.stateAmplitudeEnvelope XPlus XMinus D ∷ []))
      summed)

discreteHermitianG2 :
  (XPlus XMinus D : C3.Complex3 G0.Weld.F) →
  (displacement : ℚ) →
  1ℚ ≤ displacement →
  ∣ G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D ∣
  ≤ displacement * (two * G1.stateAmplitudeEnvelope XPlus XMinus D)
discreteHermitianG2 XPlus XMinus D displacement oneBelowDisplacement =
  let
    envelope = G1.stateAmplitudeEnvelope XPlus XMinus D
    envelopeNN = G1.stateAmplitudeEnvelopeNonnegative XPlus XMinus D

    twoEnvelopeNN : 0ℚ ≤ two * envelope
    twoEnvelopeNN =
      let
        twoNN : 0ℚ ≤ two
        twoNN = subst (0ℚ ≤_) (sym (solve (1ℚ ∷ []))) (ℚP.positive⁻¹ 1ℚ)
        instance twoNNI = nonNegative twoNN
      in
      ℚP.*-monoˡ-≤-nonNeg two envelopeNN

    oneScaled :
      1ℚ * (two * envelope)
      ≤ displacement * (two * envelope)
    oneScaled =
      let instance factorNN = nonNegative twoEnvelopeNN
      in ℚP.*-monoʳ-≤-nonNeg (two * envelope) oneBelowDisplacement

    local =
      differenceMagnitudeBelowTwoEnvelope XPlus XMinus D
  in
  ℚP.≤-trans
    local
    (subst
      (two * envelope ≤_)
      (ℚP.*-identityˡ (two * envelope))
      oneScaled)

r571DiscreteG2FromG1Closed : Bool
r571DiscreteG2FromG1Closed = true

r571RequiresFourierStateDifferentiabilityForG2 : Bool
r571RequiresFourierStateDifferentiabilityForG2 = false

r571StillRequiresSameDisplacementMultiplierTransport : Bool
r571StillRequiresSameDisplacementMultiplierTransport = true

r571StillRequiresCutoffUniformG1FamilyEnvelope : Bool
r571StillRequiresCutoffUniformG1FamilyEnvelope = true

clayPromotion : Bool
clayPromotion = false

r571DiscreteG2FromG1ClosedIsTrue :
  r571DiscreteG2FromG1Closed ≡ true
r571DiscreteG2FromG1ClosedIsTrue = refl

r571RequiresFourierStateDifferentiabilityForG2IsFalse :
  r571RequiresFourierStateDifferentiabilityForG2 ≡ false
r571RequiresFourierStateDifferentiabilityForG2IsFalse = refl
