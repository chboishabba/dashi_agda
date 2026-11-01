module DASHI.Mathematics.NumberTheory.PartitionErdosDivisorSumRecurrenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- FINAL FINITE RECURRENCE
--
-- Compose:
--   pointed-partition double count
--   -> admissible residual normal form
--   -> classical r=k*v factor-pair normal form
--   -> sigma_1 regrouping.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.NumberTheory.PartitionDivisorSumRegroupingExact as Regroup
import DASHI.Mathematics.NumberTheory.PartitionErdosAdmissibleResidualIdentityExact as AdmissibleIdentity
import DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualCardinalityExact as ClassicalCardinality
import DASHI.Mathematics.NumberTheory.PartitionErdosClassicalFactorResidualPermutationExact as ClassicalPermutation
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyCardinalityExact as Cardinality

------------------------------------------------------------------------
-- First recover the conventional (v,k) grouped double sum.

canonicalErdosFactorPairRecurrence :
  (n : Nat) →
  n * Cardinality.canonicalPartitionCount n
  ≡ Regroup.factorPairGroupedRHS n
canonicalErdosFactorPairRecurrence n =
  trans
    (AdmissibleIdentity.canonicalErdosAdmissibleResidualIdentity n)
    (trans
      (sym (ClassicalPermutation.classicalAdmissibleUnitFold n))
      (ClassicalCardinality.classicalFactorResidualUnitFoldEqualsGroupedRHS n))

------------------------------------------------------------------------
-- Then group factor pairs by r and identify their v-weight with sigma_1(r).

canonicalErdosDivisorSumRecurrence :
  (n : Nat) →
  n * Cardinality.canonicalPartitionCount n
  ≡ Regroup.divisorSumRHS n
canonicalErdosDivisorSumRecurrence n =
  trans
    (canonicalErdosFactorPairRecurrence n)
    (Regroup.factorPairGroupedEqualsDivisorSum n)

------------------------------------------------------------------------
-- Expanded reading of the right-hand side:
--
--   divisorSumRHS n
--   = sum_{r=1}^n sigma_1(r) * p_DASHI(n-r).
--
-- Therefore this owner closes the arbitrary-n finite recurrence
--
--   n p(n) = sum_{r=1}^n sigma_1(r) p(n-r)
--
-- for the canonical multiplicity-vector partition count.
------------------------------------------------------------------------
