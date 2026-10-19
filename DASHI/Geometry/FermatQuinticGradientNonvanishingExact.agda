module DASHI.Geometry.FermatQuinticGradientNonvanishingExact where

-- Concrete algebraic singularity argument for the Fermat quintic.
-- The assumptions are precisely the two facts required in a field:
-- characteristic is not five, and a fourth power vanishes only at zero.
-- No appeal to dimension counting is involved.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

record QuinticField : Set₁ where
  field
    Scalar : Set
    zero : Scalar
    fourthPower : Scalar → Scalar
    fiveTimes : Scalar → Scalar
    fourthPowerZero : ∀ x → fourthPower x ≡ zero → x ≡ zero
    fiveTimesZero : ∀ x → fiveTimes x ≡ zero → x ≡ zero

open QuinticField public

record ProjectiveFiveCoordinates (F : QuinticField) : Set where
  constructor coordinates
  field
    z0 z1 z2 z3 z4 : Scalar F
    atLeastOneNonzero :
      z0 ≡ zero F →
      z1 ≡ zero F →
      z2 ≡ zero F →
      z3 ≡ zero F →
      z4 ≡ zero F →
      ⊥

open ProjectiveFiveCoordinates public

record QuinticGradientZero (F : QuinticField)
    (z : ProjectiveFiveCoordinates F) : Set where
  field
    d0 : fiveTimes F (fourthPower F (z0 z)) ≡ zero F
    d1 : fiveTimes F (fourthPower F (z1 z)) ≡ zero F
    d2 : fiveTimes F (fourthPower F (z2 z)) ≡ zero F
    d3 : fiveTimes F (fourthPower F (z3 z)) ≡ zero F
    d4 : fiveTimes F (fourthPower F (z4 z)) ≡ zero F

open QuinticGradientZero public

fermatQuinticHasNoSimultaneousGradientZero :
  (F : QuinticField) →
  (z : ProjectiveFiveCoordinates F) →
  QuinticGradientZero F z → ⊥
fermatQuinticHasNoSimultaneousGradientZero F z grad =
  atLeastOneNonzero z
    (fourthPowerZero F (z0 z) (fiveTimesZero F _ (d0 grad)))
    (fourthPowerZero F (z1 z) (fiveTimesZero F _ (d1 grad)))
    (fourthPowerZero F (z2 z) (fiveTimesZero F _ (d2 grad)))
    (fourthPowerZero F (z3 z) (fiveTimesZero F _ (d3 grad)))
    (fourthPowerZero F (z4 z) (fiveTimesZero F _ (d4 grad)))

-- The derivative of sum(z_i^5) is 5 z_i^4.
-- The field operations and polynomial differentiation identities remain
-- external to this exact nonvanishing core; its assumptions are explicit.
