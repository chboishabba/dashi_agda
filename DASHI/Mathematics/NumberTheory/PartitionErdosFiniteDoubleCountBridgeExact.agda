module DASHI.Mathematics.NumberTheory.PartitionErdosFiniteDoubleCountBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- REPO CROSS-POLLINATION
--
-- The finite Galerkin-incidence lane already proves equality of global sums by
-- promoting a proof-relevant reindexing to an exact list permutation and then
-- transporting the fold across that permutation.  FiniteWeightedReindexExact
-- extracts that machinery without any fluid-specific carrier.
--
-- DASHI CONTRIBUTION
--
-- Isolate the genuinely combinatorial heart of the Erdos partition identity.
-- For each n, one finite enumeration counts the n*p(n) marked mass of
-- partitions of n.  A deletion map sends it to the finite residual enumeration
-- underlying
--
--   sum_{v >= 1} sum_{k >= 1} v p(n-kv).
--
-- Once deletion is injective and its image has exactly the same members as the
-- residual enumeration, the generic unique-membership theorem promotes it to
-- a list permutation.  Weight preservation then proves the two finite folds
-- equal.  The residual double sum below is definitionally that weighted fold;
-- no arbitrary right-hand-side function is supplied by an instantiation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.List.Base using (map)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.Unique.Propositional as Unique
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
import Data.List.Relation.Binary.Permutation.Propositional as Perm
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex

------------------------------------------------------------------------
-- Concrete owners instantiate this record with actual partition, marked and
-- residual carriers.  The marked fold is the only evaluation law required for
-- n*p(n); the residual RHS is computed directly from its enumeration.

record ErdosDeletionFibreSystem : Set₁ where
  field
    PartitionCount : Nat → Nat

    Marked Residual : Nat → Set

    markedEnumeration : (n : Nat) → List (Marked n)
    residualEnumeration : (n : Nat) → List (Residual n)

    delete : {n : Nat} → Marked n → Residual n

    markedWeight : {n : Nat} → Marked n → Nat
    residualWeight : {n : Nat} → Residual n → Nat

    markedUnique : (n : Nat) → Unique.Unique (markedEnumeration n)
    residualUnique : (n : Nat) → Unique.Unique (residualEnumeration n)

    deleteInjective :
      {n : Nat} {left right : Marked n} →
      delete left ≡ delete right → left ≡ right

    mappedDeleteForward :
      {n : Nat} {residual : Residual n} →
      residual ∈ map delete (markedEnumeration n) →
      residual ∈ residualEnumeration n

    mappedDeleteBackward :
      {n : Nat} {residual : Residual n} →
      residual ∈ residualEnumeration n →
      residual ∈ map delete (markedEnumeration n)

    deletePreservesWeight :
      {n : Nat} (marked : Marked n) →
      markedWeight marked ≡ residualWeight (delete marked)

    markedFoldEvaluation :
      (n : Nat) →
      Reindex.foldNat markedWeight (markedEnumeration n)
      ≡ n * PartitionCount n

open ErdosDeletionFibreSystem public

------------------------------------------------------------------------
-- Canonical finite RHS associated with the residual enumeration.

ErdosResidualDoubleSum :
  (system : ErdosDeletionFibreSystem) → Nat → Nat
ErdosResidualDoubleSum system n =
  Reindex.foldNat
    (residualWeight system)
    (residualEnumeration system n)

------------------------------------------------------------------------
-- The NS-derived finite-enumeration machinery closes the reindexing step.

deletePermutation :
  (system : ErdosDeletionFibreSystem) →
  (n : Nat) →
  map (delete system) (markedEnumeration system n)
    Perm.↭ residualEnumeration system n
deletePermutation system n =
  Reindex.uniqueMembershipEquivalenceToPermutation
    (UniqueP.map⁺ (deleteInjective system) (markedUnique system n))
    (residualUnique system n)
    (mappedDeleteForward system)
    (mappedDeleteBackward system)

markedResidualFoldEquality :
  (system : ErdosDeletionFibreSystem) →
  (n : Nat) →
  Reindex.foldNat (markedWeight system) (markedEnumeration system n)
  ≡ ErdosResidualDoubleSum system n
markedResidualFoldEquality system n =
  Reindex.weightedMappedPermutationPreservesFold
    (markedWeight system)
    (residualWeight system)
    (delete system)
    (markedEnumeration system n)
    (deletePreservesWeight system)
    (deletePermutation system n)

------------------------------------------------------------------------
-- Arbitrary-n Erdos finite double-count identity as a derived theorem.

erdosIdentityFromDeletionFibre :
  (system : ErdosDeletionFibreSystem) →
  (n : Nat) →
  n * PartitionCount system n ≡ ErdosResidualDoubleSum system n
erdosIdentityFromDeletionFibre system n =
  trans
    (sym (markedFoldEvaluation system n))
    (markedResidualFoldEquality system n)

------------------------------------------------------------------------
-- Identification with the conventional written double sum is a separate
-- grouping theorem.  This prevents an arbitrary Nat-valued RHS from being
-- smuggled into the finite reindexing theorem.

record ClassicalErdosDoubleSumIdentification
    (system : ErdosDeletionFibreSystem) : Set₁ where
  field
    classicalDoubleSum : Nat → Nat
    residualGroupingExact :
      (n : Nat) →
      ErdosResidualDoubleSum system n ≡ classicalDoubleSum n

open ClassicalErdosDoubleSumIdentification public

erdosIdentityWithClassicalGrouping :
  (system : ErdosDeletionFibreSystem) →
  (identification : ClassicalErdosDoubleSumIdentification system) →
  (n : Nat) →
  n * PartitionCount system n ≡ classicalDoubleSum identification n
erdosIdentityWithClassicalGrouping system identification n =
  trans
    (erdosIdentityFromDeletionFibre system n)
    (residualGroupingExact identification n)

------------------------------------------------------------------------
-- No analytic convergence, eta modularity, or asymptotic estimate is used to
-- establish the finite identity.  The remaining partition-specific work is to
-- construct the concrete residual carrier whose grouped fold is literally
-- sum_v sum_k v p(n-kv).
