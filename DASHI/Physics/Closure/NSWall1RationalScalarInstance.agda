module DASHI.Physics.Closure.NSWall1RationalScalarInstance where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (ℤ)
import Data.Integer.Properties as ℤ
open import Data.Rational.Base as ℚ
  using (ℚ; 0ℚ; 1ℚ; ½; _+_; _-_; _*_; -_; _≤_; ∣_∣; _/_)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import DASHI.Physics.Closure.NSIntegerFourierLattice
open import DASHI.Physics.Closure.NSWall1CanonicalModePacket
open import DASHI.Physics.Closure.NSWall1ExactEvaluationCarrier

------------------------------------------------------------------------
-- Exact normalized rational carrier for the canonical Wall-1 packet.
------------------------------------------------------------------------

rationalScalarAlgebra : ExactScalarAlgebra ℚ
rationalScalarAlgebra = record
  { zero = 0ℚ
  ; one = 1ℚ
  ; add = _+_
  ; subtract = _-_
  ; multiply = _*_
  ; negate = -_
  ; order = _≤_
  ; integerEmbed = λ z → z / 1
  }

modeDeltaℚ : FourierMode → FourierMode → ℚ
modeDeltaℚ (mode x y z) (mode x′ y′ z′)
  with x ℤ.≟ x′ | y ℤ.≟ y′ | z ℤ.≟ z′
... | yes _ | yes _ | yes _ = 1ℚ
... | _     | _     | _     = 0ℚ

packetInverseNormSquared : FourierMode → ℚ
packetInverseNormSquared k =
  modeDeltaℚ k p100 +
  modeDeltaℚ k p010 +
  modeDeltaℚ k p001 +
  ½ * modeDeltaℚ k p110 +
  ½ * modeDeltaℚ k p101 +
  ½ * modeDeltaℚ k p011

rationalL1Majorant : Vec3 ℚ → ℚ
rationalL1Majorant v = ∣ x v ∣ + ∣ y v ∣ + ∣ z v ∣

rationalFourierEvaluation :
  ExactFourierEvaluation ℚ rationalScalarAlgebra
rationalFourierEvaluation = record
  { inverseNormSquared = packetInverseNormSquared
  ; modeDelta = modeDeltaℚ
  ; vectorMajorant = rationalL1Majorant
  }

rationalHalfPlusHalf : ½ + ½ ≡ 1ℚ
rationalHalfPlusHalf = refl

rationalDelta100100 : modeDeltaℚ p100 p100 ≡ 1ℚ
rationalDelta100100 = refl

rationalDelta010010 : modeDeltaℚ p010 p010 ≡ 1ℚ
rationalDelta010010 = refl

rationalDelta001001 : modeDeltaℚ p001 p001 ≡ 1ℚ
rationalDelta001001 = refl

rationalDelta110110 : modeDeltaℚ p110 p110 ≡ 1ℚ
rationalDelta110110 = refl

rationalDelta101101 : modeDeltaℚ p101 p101 ≡ 1ℚ
rationalDelta101101 = refl

rationalDelta011011 : modeDeltaℚ p011 p011 ≡ 1ℚ
rationalDelta011011 = refl

rationalInverseNorm100 : packetInverseNormSquared p100 ≡ 1ℚ
rationalInverseNorm100 = refl

rationalInverseNorm010 : packetInverseNormSquared p010 ≡ 1ℚ
rationalInverseNorm010 = refl

rationalInverseNorm001 : packetInverseNormSquared p001 ≡ 1ℚ
rationalInverseNorm001 = refl

rationalInverseNorm110 : packetInverseNormSquared p110 ≡ ½
rationalInverseNorm110 = refl

rationalInverseNorm101 : packetInverseNormSquared p101 ≡ ½
rationalInverseNorm101 = refl

rationalInverseNorm011 : packetInverseNormSquared p011 ≡ ½
rationalInverseNorm011 = refl
