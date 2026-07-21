module DASHI.Physics.Closure.NSPeriodicConcreteDyadicPartition where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)

------------------------------------------------------------------------
-- Exact natural-number arithmetic for the rational max-norm hat multiplier.
------------------------------------------------------------------------

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = 2 * pow2 n

shellLower shellPeak shellUpper : Nat → Nat
shellLower j = pow2 j
shellPeak j = pow2 (suc j)
shellUpper j = pow2 (suc (suc j))

-- For a hat with maximal slope 2^(1-K) and low separation
-- |p|_infinity <= 2^(K-R), the normalized multiplier gain is 2^(1-R).
radiusEightMultiplierNumerator radiusEightMultiplierDenominator : Nat
radiusEightMultiplierNumerator = 1
radiusEightMultiplierDenominator = pow2 7

radiusEightMultiplierDenominatorIs128 :
  radiusEightMultiplierDenominator ≡ 128
radiusEightMultiplierDenominatorIs128 = refl

-- At s = 7/2 the high-shell exponent is exactly one.  Starting R shells away,
-- the complete geometric series is 2^(-R)/(1-1/2) = 2^(1-R).
farHighGeometricNumerator farHighGeometricDenominator : Nat
farHighGeometricNumerator = 1
farHighGeometricDenominator = pow2 7

farHighGeometricDenominatorIs128 :
  farHighGeometricDenominator ≡ 128
farHighGeometricDenominatorIs128 = refl

rationalHatFiniteCheckPromotesMeanValueTheorem : Bool
rationalHatFiniteCheckPromotesMeanValueTheorem = false
