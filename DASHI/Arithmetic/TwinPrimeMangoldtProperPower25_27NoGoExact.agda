module DASHI.Arithmetic.TwinPrimeMangoldtProperPower25_27NoGoExact where

------------------------------------------------------------------------
-- M14 NO-GO: THE GAP-2 PAIR (25,27) CONSISTS OF PROPER POWERS.
--
-- 25=5^2, 27=3^3. Both are proper powers of actual primes,
-- but both are composite. Hence a finite Mangoldt correlation
-- cannot be interpreted as a sum over genuine prime pairs
-- without explicitly subtracting proper-prime-power terms.
--
-- Uses original Nat primality/refutation and factorable-lift
-- proof owner. This does NOT claim any analytic lower bound.
-- Source-written, Agda kernel pending. 2026-10-30.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁)
import Data.Nat.Primality as Prime
import DASHI.Analysis.RiemannPrimePowerArithmetic as Power
import DASHI.Arithmetic.FiniteTwinSieveFactorableLiftExact as Factors
import DASHI.Arithmetic.TwinPrimeSixWheelExact as Twin

fiveSquaredIs25 : Power.natPow 5 2 ≡ 25
fiveSquaredIs25 = refl

threeCubedIs27 : Power.natPow 3 3 ≡ 27
threeCubedIs27 = refl

gapTwoBetweenPowers : 25 + Twin.two ≡ 27
gapTwoBetweenPowers = refl

bothAreProperPowerValues :
  (Power.natPow 5 2 ≡ 25)
  × (Power.natPow 3 3 ≡ 27)
bothAreProperPowerValues = fiveSquaredIs25 , threeCubedIs27

twentyFiveHasNontrivialFactors :
  Factors.TwoNontrivialFactors 25
twentyFiveHasNontrivialFactors =
  Factors.twoNontrivialFactors 3 3 refl

twentySevenHasNontrivialFactors :
  Factors.TwoNontrivialFactors 27
twentySevenHasNontrivialFactors =
  Factors.twoNontrivialFactors 1 7 refl

twentyFiveIsComposite : Prime.Composite 25
twentyFiveIsComposite =
  Factors.twoNontrivialFactorsAreComposite 25
    twentyFiveHasNontrivialFactors

twentySevenIsComposite : Prime.Composite 27
twentySevenIsComposite =
  Factors.twoNontrivialFactorsAreComposite 27
    twentySevenHasNontrivialFactors

notTwinAtTwentyFive : Twin.TwinPrimeAt 25 → ⊥
notTwinAtTwentyFive pair =
  Factors.twoNontrivialFactorsRefutePrime
    25 twentyFiveHasNontrivialFactors (proj₁ pair)

-- This example refutes the tempting shortcut
-- "nonzero Lambda(n)*Lambda(n+2) always implies twin primes".
-- A fully formal nonzero statement additionally requires a
-- concrete scalar with log(3),log(5)>0, which this module
-- intentionally does not assume or fabricate.
