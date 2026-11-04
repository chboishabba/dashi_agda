{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21FinFreePairwiseQuadraticCountExact where

------------------------------------------------------------------------
-- N21 FIN-FREE ENDPOINT PAIRWISE SCAN: EXACT *COMPARISON-COUNT* CLOCK.
--
-- At the j-th signed edge the original sparse runtime contains 2*j
-- previous endpoint assignments. Both the new u and v must be checked
-- against those, so the full-scan upper count is 4*j address equality
-- tests. Summing over m edges gives exactly 2*m*(m-1).
--
-- This is a concrete arithmetic result for the source-owned
-- endpointConsistent loop, NOT a polynomial-time Turing-machine
-- verifier certificate. Equality of potentially long binary indices,
-- gamma parser cost, signed arithmetic, input/output copying and
-- total tape transitions still require explicit clocks.
--
-- Richard Karp (1972); DASHI original binary-native sparse runtime.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_∸_)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Nat.Tactic.RingSolver using (solve)
open import Agda.Builtin.List using ([]; _∷_)

-- Number of comparisons in the first j complete edge scans of the
-- full-history deterministic pairwise checker.
maxAddressComparisons : Nat → Nat
maxAddressComparisons zero = zero
maxAddressComparisons (suc j) =
  maxAddressComparisons j + 4 * j

comparisonStepSemiring :
  (j : Nat) →
  (2 * suc j * j) + (4 * suc j)
    ≡ 2 * suc (suc j) * suc j
comparisonStepSemiring j = solve (j ∷ [])

-- Closed quadratic count independent of the declared vertex n.
-- For m=0, m=1 the loop never scans an earlier endpoint.
maxAddressComparisonsClosed :
  (m : Nat) →
  maxAddressComparisons m ≡ 2 * m * (m ∸ suc zero)
maxAddressComparisonsClosed zero = refl
maxAddressComparisonsClosed (suc zero) = refl
maxAddressComparisonsClosed (suc (suc j))
  rewrite maxAddressComparisonsClosed (suc j) =
  comparisonStepSemiring j
