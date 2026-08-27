module DASHI.Mathematics.NumberTheory.PartitionErdosAdmissibleResidualIdentityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- The strict deletion-image RHS is replaced here by the independently
-- generated admissible residual normal form (mu,v,j,u).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Mathematics.NumberTheory.PartitionErdosAdmissibleResidualEnumerationExact as Admissible
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyCardinalityExact as Cardinality
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeySystemExact as System
import DASHI.Mathematics.NumberTheory.PartitionErdosResidualKeyPermutationExact as Permutation
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteDoubleCountBridgeExact as Bridge

admissibleResidualUnitFold : Nat → Nat
admissibleResidualUnitFold n =
  Reindex.foldNat (λ _ → 1) (Admissible.admissibleResidualEnumeration n)

residualDoubleSumEqualsAdmissibleNormalForm :
  (n : Nat) →
  Bridge.ErdosResidualDoubleSum System.canonicalErdosFiniteKeySystem n
  ≡ admissibleResidualUnitFold n
residualDoubleSumEqualsAdmissibleNormalForm n =
  Reindex.foldPermutationInvariant
    (λ _ → 1)
    (Permutation.residualNormalFormPermutation n)

canonicalErdosAdmissibleResidualIdentity :
  (n : Nat) →
  n * Cardinality.canonicalPartitionCount n
  ≡ admissibleResidualUnitFold n
canonicalErdosAdmissibleResidualIdentity n =
  trans
    (System.canonicalErdosKeyIdentity n)
    (residualDoubleSumEqualsAdmissibleNormalForm n)

------------------------------------------------------------------------
-- This is now independent of the deletion-image presentation.  The remaining
-- arithmetic grouping is to evaluate this normal-form unit fold by r=(j+1)v.
------------------------------------------------------------------------
