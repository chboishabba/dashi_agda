module DASHI.Mathematics.NumberTheory.PartitionDivisorSumRecurrencePrefixExact where

------------------------------------------------------------------------
-- DIVISOR-SUM PRESENTATION OF THE PARTITION RECURRENCE
--
-- Grouping the Erdos residual coordinates by r = k*v turns
--
--   sum_v sum_k v p(n-kv)
--
-- into
--
--   sum_{r=1}^n sigma1(r) p(n-r).
--
-- This module gives the executable regrouped expression and checks it on the
-- already certified partition prefix n=1..5.  The all-n grouping permutation
-- remains a separate theorem target; the finite regression is not promoted to
-- that theorem by coincidence alone.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Base using (_∸_)

import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Mathematics.NumberTheory.FiniteDivisorSumExact as Divisor
import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke

------------------------------------------------------------------------
-- Certified finite partition prefix 1,1,2,3,5,7.

pPrefix : Nat → Nat
pPrefix zero = 1
pPrefix (suc zero) = 1
pPrefix (suc (suc zero)) = 2
pPrefix (suc (suc (suc zero))) = 3
pPrefix (suc (suc (suc (suc zero)))) = 5
pPrefix (suc (suc (suc (suc (suc zero))))) = 7
pPrefix _ = 0

divisorGroupedRhs : Nat → Nat
divisorGroupedRhs n =
  Reindex.foldNat
    (λ r → Divisor.sigma1 r * pPrefix (n ∸ r))
    (Hecke.oneTo n)

------------------------------------------------------------------------
-- Exact regression of n*p(n) = sum_r sigma1(r)p(n-r).

divisorRecurrenceAt1 : 1 * pPrefix 1 ≡ divisorGroupedRhs 1
divisorRecurrenceAt1 = refl

divisorRecurrenceAt2 : 2 * pPrefix 2 ≡ divisorGroupedRhs 2
divisorRecurrenceAt2 = refl

divisorRecurrenceAt3 : 3 * pPrefix 3 ≡ divisorGroupedRhs 3
divisorRecurrenceAt3 = refl

divisorRecurrenceAt4 : 4 * pPrefix 4 ≡ divisorGroupedRhs 4
divisorRecurrenceAt4 = refl

divisorRecurrenceAt5 : 5 * pPrefix 5 ≡ divisorGroupedRhs 5
divisorRecurrenceAt5 = refl

record DivisorGroupingCompletion : Set₁ where
  field
    factorPairToProductGradeExact : Set
    productGradeToDivisorExact : Set
    factorPairGroupingPermutationExact : Set
    arbitraryNDivisorRecurrenceExact : (n : Nat) → Set

------------------------------------------------------------------------
-- The remaining theorem is precisely the all-n finite regrouping by r=k*v.
------------------------------------------------------------------------
