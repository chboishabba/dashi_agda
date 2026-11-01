module DASHI.Analysis.BernoulliFourCubicTelescopingExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing

import DASHI.Analysis.BernoulliFourCubicFiniteDifferenceExact as B4

------------------------------------------------------------------------
-- FINITE CUBIC SUM TELESCOPING THROUGH B4
--
-- With natQ n the canonical repeated-one embedding and
--
--   S3(n) = sum_{k=0}^{n-1} k^3,
--
-- prove exactly
--
--   B4(n) - B4(0) = 4 S3(n).
--
-- This closes the finite-sum Bernoulli correspondence without any analytic
-- continuation, regularisation, or zeta semantics.
------------------------------------------------------------------------

natQ : Nat → ℚ
natQ zero = 0ℚ
natQ (suc n) = natQ n + 1ℚ

sumCubesQ : Nat → ℚ
sumCubesQ zero = 0ℚ
sumCubesQ (suc n) = sumCubesQ n + B4.cube (natQ n)

open import Relation.Binary.PropositionalEquality using (sym; trans; cong₂)

subSplit : (a b c : ℚ) → a - c ≡ (a - b) + (b - c)
subSplit a b c = ℚRing.solve (a ∷ b ∷ c ∷ [])

distribFour : (k c s : ℚ) → (k * c) + (k * s) ≡ k * (s + c)
distribFour k c s = ℚRing.solve (k ∷ c ∷ s ∷ [])

bernoulliFourTelescopesCubicSum :
  (n : Nat) →
  B4.bernoulliFourPolynomial (natQ n)
    - B4.bernoulliFourPolynomial 0ℚ
  ≡ B4.four * sumCubesQ n
bernoulliFourTelescopesCubicSum zero = refl
bernoulliFourTelescopesCubicSum (suc n) =
  trans (subSplit A B C)
    (trans (cong₂ _+_ stepDiff stepIH)
           (distribFour B4.four (B4.cube (natQ n)) (sumCubesQ n)))
  where
    A = B4.bernoulliFourPolynomial (natQ (suc n))
    B = B4.bernoulliFourPolynomial (natQ n)
    C = B4.bernoulliFourPolynomial 0ℚ

    stepDiff : A - B ≡ B4.four * B4.cube (natQ n)
    stepDiff = B4.bernoulliFourFiniteDifferenceIsFourCubes (natQ n)

    stepIH : B - C ≡ B4.four * sumCubesQ n
    stepIH = bernoulliFourTelescopesCubicSum n

record FiniteCubicBernoulliSumReceipt : Set where
  field
    cutoff : Nat
    cubicPartialSum : ℚ
    cubicPartialSumLaw : cubicPartialSum ≡ sumCubesQ cutoff
    bernoulliTelescopingLaw :
      B4.bernoulliFourPolynomial (natQ cutoff)
        - B4.bernoulliFourPolynomial 0ℚ
      ≡ B4.four * cubicPartialSum

open FiniteCubicBernoulliSumReceipt public

buildFiniteCubicBernoulliSumReceipt :
  (n : Nat) → FiniteCubicBernoulliSumReceipt
buildFiniteCubicBernoulliSumReceipt n = record
  { cutoff = n
  ; cubicPartialSum = sumCubesQ n
  ; cubicPartialSumLaw = refl
  ; bernoulliTelescopingLaw = bernoulliFourTelescopesCubicSum n
  }
