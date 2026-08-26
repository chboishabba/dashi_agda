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
-- equal.  Thus the arbitrary-n identity no longer appears as an opaque Set:
-- it is a theorem derived from explicit enumeration/fibre obligations.
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
-- Concrete owners instantiate this record with an actual partition carrier,
-- actual finite marked/residual enumerations, and the bounded Erdos double sum.

record ErdosDeletionFibreSystem : Set₁ where
  field
    PartitionCount : Nat → Nat
    ErdosDoubleSum : Nat → Nat

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

    residualFoldEvaluation :
      (n : Nat) →
      Reindex.foldNat residualWeight (residualEnumeration n)
      ≡ ErdosDoubleSum n

open ErdosDeletionFibreSystem public

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
  ≡ Reindex.foldNat (residualWeight system) (residualEnumeration system n)
markedResidualFoldEquality system n =
  Reindex.weightedMappedPermutationPreservesFold
    (markedWeight system)
    (residualWeight system)
    (delete system)
    (markedEnumeration system n)
    (deletePreservesWeight system)
    (deletePermutation system n)

------------------------------------------------------------------------
-- Arbitrary-n Erdos identity as a derived theorem.

erdosIdentityFromDeletionFibre :
  (system : ErdosDeletionFibreSystem) →
  (n : Nat) →
  n * PartitionCount system n ≡ ErdosDoubleSum system n
erdosIdentityFromDeletionFibre system n =
  trans
    (sym (markedFoldEvaluation system n))
    (trans
      (markedResidualFoldEquality system n)
      (residualFoldEvaluation system n))

------------------------------------------------------------------------
-- The theorem above leaves concrete partition construction as the only domain
-- obligation.  In particular, no analytic convergence, eta modularity, or
-- asymptotic estimate is used to establish the finite identity.
