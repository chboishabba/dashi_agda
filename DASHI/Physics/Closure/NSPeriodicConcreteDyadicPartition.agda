module DASHI.Physics.Closure.NSPeriodicConcreteDyadicPartition where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)

------------------------------------------------------------------------
-- Exact natural-number arithmetic for the rational max-norm hat multiplier.
--
-- Shell zero has support [0,2] and peak 1.  Every positive shell K has support
-- [2^(K-1),2^(K+1)] and peak 2^K, exactly matching the Python carrier.
------------------------------------------------------------------------

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = 2 * pow2 n

shellLower shellPeak shellUpper : Nat → Nat
shellLower zero = 0
shellLower (suc K) = pow2 K
shellPeak zero = 1
shellPeak (suc K) = pow2 (suc K)
shellUpper zero = 2
shellUpper (suc K) = pow2 (suc (suc K))

shellOneLowerRegression : shellLower 1 ≡ 1
shellOneLowerRegression = refl

shellOnePeakRegression : shellPeak 1 ≡ 2
shellOnePeakRegression = refl

shellOneUpperRegression : shellUpper 1 ≡ 4
shellOneUpperRegression = refl

-- For a positive-shell hat with maximal slope 2^(1-K) and low separation
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
