module DASHI.Mathematics.NumberTheory.FiniteFactorPairDivisorSumExact where

------------------------------------------------------------------------
-- FINITE FACTOR PAIRS AND THE FIRST DIVISOR SUM
--
-- This is the arithmetic regrouping kernel behind
--
--   sum_{v>=1} sum_{k>=1} v * a(n-kv)
--
-- when terms are grouped by r = k*v.  We reuse the same positive-integer
-- scanner and divisibility decision already used by the Hecke and sigma1
-- owners.  A divisor witness carries its quotient, so a factor pair is
-- proof-bearing rather than reconstructed by unchecked division.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.List.Base using (filter)
open import Data.Nat.Divisibility using (_∣_; _∣?_)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteDivisorSumExact as Divisor
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex

------------------------------------------------------------------------
-- A positive divisor d of r together with the exact complementary factor k.
-- Positivity of d is supplied by the source enumeration oneTo r.

record FactorPair (r : Nat) : Set where
  constructor factorPair
  field
    divisor : Nat
    quotient : Nat
    productExact : r ≡ quotient * divisor

open FactorPair public

factorWeight : ∀ {r : Nat} → FactorPair r → Nat
factorWeight = divisor

------------------------------------------------------------------------
-- Proof-bearing factor-pair enumeration using the divisibility witness itself.

factorPairsFrom : (r : Nat) → List Nat → List (FactorPair r)
factorPairsFrom r [] = []
factorPairsFrom r (d ∷ ds) with d ∣? r
... | yes dividesProof =
  factorPair
    d
    (_∣_.quotient dividesProof)
    (_∣_.equality dividesProof)
  ∷ factorPairsFrom r ds
... | no _ = factorPairsFrom r ds

factorPairs : (r : Nat) → List (FactorPair r)
factorPairs r = factorPairsFrom r (Hecke.oneTo r)

factorPairWeightSum : Nat → Nat
factorPairWeightSum r = Reindex.foldNat factorWeight (factorPairs r)

------------------------------------------------------------------------
-- The factor-pair weighted fold is exactly the divisor filter fold.  The proof
-- follows the same divisibility decision branch-by-branch, so no quotient
-- uniqueness theorem is required.

factorPairsFromWeightEqualsDivisorFilter :
  (r : Nat) (candidates : List Nat) →
  Reindex.foldNat factorWeight (factorPairsFrom r candidates)
  ≡ Reindex.foldNat (λ d → d)
      (filter (λ d → d ∣? r) candidates)
factorPairsFromWeightEqualsDivisorFilter r [] = refl
factorPairsFromWeightEqualsDivisorFilter r (d ∷ ds) with d ∣? r
... | yes proof =
  cong (d +_) (factorPairsFromWeightEqualsDivisorFilter r ds)
... | no _ = factorPairsFromWeightEqualsDivisorFilter r ds

factorPairWeightSumIsSigma1 :
  (r : Nat) → factorPairWeightSum r ≡ Divisor.sigma1 r
factorPairWeightSumIsSigma1 r =
  factorPairsFromWeightEqualsDivisorFilter r (Hecke.oneTo r)

------------------------------------------------------------------------
-- Closed regressions expose the intended grouping values.

factorPairWeightSum1 : factorPairWeightSum 1 ≡ 1
factorPairWeightSum1 = trans (factorPairWeightSumIsSigma1 1) Divisor.sigma1One

factorPairWeightSum2 : factorPairWeightSum 2 ≡ 3
factorPairWeightSum2 = trans (factorPairWeightSumIsSigma1 2) Divisor.sigma1Two

factorPairWeightSum3 : factorPairWeightSum 3 ≡ 4
factorPairWeightSum3 = trans (factorPairWeightSumIsSigma1 3) Divisor.sigma1Three

factorPairWeightSum4 : factorPairWeightSum 4 ≡ 7
factorPairWeightSum4 = trans (factorPairWeightSumIsSigma1 4) Divisor.sigma1Four

factorPairWeightSum6 : factorPairWeightSum 6 ≡ 12
factorPairWeightSum6 = trans (factorPairWeightSumIsSigma1 6) Divisor.sigma1Six

------------------------------------------------------------------------
-- This theorem is finite arithmetic only.  The next partition-specific bridge
-- shows that residual coordinates (v,k,mu,u) grouped by r=k*v are enumerated
-- by these factor pairs together with a grade-(n-r) partition.
------------------------------------------------------------------------
