module DASHI.Mathematics.NumberTheory.PartitionDivisorSumRegroupingExact where

------------------------------------------------------------------------
-- ERDOS FACTOR-PAIR REGROUPING -> SIGMA_1 CONVOLUTION
--
-- The combinatorial deletion route naturally produces generator/copy pairs
-- (v,k).  Grouping by r=k*v replaces the total v-weight of all factor pairs of
-- r by sigma1(r).  This owner proves that regrouping for the canonical all-n
-- multiplicity-vector partition count, independently of the still-separate
-- cell/residual enumeration permutation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_; _∸_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Moonshine.ClassicalHeckeWeightKSmallWordExact as Hecke
import DASHI.Mathematics.NumberTheory.FiniteDivisorSumExact as Divisor
import DASHI.Mathematics.NumberTheory.FiniteFactorPairDivisorSumExact as Factor
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityEnumerationExact as Enumeration

------------------------------------------------------------------------
-- Canonical partition count owned by the unique multiplicity-vector list.

partitionCount : Nat → Nat
partitionCount n = Reindex.listLength (Enumeration.partitionMultiplicityVectors n)

------------------------------------------------------------------------
-- Two presentations of the same finite convolution.

factorPairGroupedRHS : Nat → Nat
factorPairGroupedRHS n =
  Reindex.foldNat
    (λ r → Factor.factorPairWeightSum r * partitionCount (n ∸ r))
    (Hecke.oneTo n)

divisorSumRHS : Nat → Nat
divisorSumRHS n =
  Reindex.foldNat
    (λ r → Divisor.sigma1 r * partitionCount (n ∸ r))
    (Hecke.oneTo n)

------------------------------------------------------------------------
-- Pointwise coefficient identification closes the arbitrary-n regrouping.

factorPairTermIsDivisorTerm :
  (n r : Nat) →
  Factor.factorPairWeightSum r * partitionCount (n ∸ r)
  ≡ Divisor.sigma1 r * partitionCount (n ∸ r)
factorPairTermIsDivisorTerm n r =
  cong
    (_* partitionCount (n ∸ r))
    (Factor.factorPairWeightSumIsSigma1 r)

factorPairGroupedEqualsDivisorSum :
  (n : Nat) → factorPairGroupedRHS n ≡ divisorSumRHS n
factorPairGroupedEqualsDivisorSum n =
  Reindex.foldPointwise
    (λ r → Factor.factorPairWeightSum r * partitionCount (n ∸ r))
    (λ r → Divisor.sigma1 r * partitionCount (n ∸ r))
    (Hecke.oneTo n)
    (factorPairTermIsDivisorTerm n)

------------------------------------------------------------------------
-- This is an all-n theorem, but deliberately not yet the recurrence
--
--   n*p(n) = divisorSumRHS n.
--
-- That final equality is obtained by composing this regrouping theorem with
-- the concrete whole-family cell/residual counting theorem once its strict
-- finite data enumeration is wired into ErdosDeletionFibreSystem.
------------------------------------------------------------------------
