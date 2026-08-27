module DASHI.Mathematics.NumberTheory.PartitionCanonicalDeletionFibreExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- DASHI CROSS-POLLINATION
--
-- PartitionMarkedUnitEnumerationExact proves that pairing every grade-n
-- partition with Fin n gives exactly n copies per partition.  The generic
-- finite deletion-fibre theorem therefore does not need a caller-supplied
-- proof of the left-hand count n*p(n): it is constructed canonically.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (map)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.Unique.Propositional as Unique
open import Data.Product using (_×_)

import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Mathematics.NumberTheory.PartitionMarkedUnitEnumerationExact as Mark
import DASHI.Mathematics.NumberTheory.PartitionErdosFiniteDoubleCountBridgeExact as DoubleCount

------------------------------------------------------------------------
-- Partition-specific input after generic finite counting has been removed.

record CanonicalPartitionDeletionData : Set₁ where
  field
    Partition Residual : Nat → Set

    partitionEnumeration : (n : Nat) → List (Partition n)
    residualEnumeration : (n : Nat) → List (Residual n)

    partitionEnumerationUnique :
      (n : Nat) → Unique.Unique (partitionEnumeration n)

    markedEnumerationUnique :
      (n : Nat) →
      Unique.Unique
        (Mark.markEnumeration {n = n} (partitionEnumeration n))

    residualEnumerationUnique :
      (n : Nat) → Unique.Unique (residualEnumeration n)

    delete :
      {n : Nat} → Partition n × Fin n → Residual n

    residualWeight :
      {n : Nat} → Residual n → Nat

    deleteInjective :
      {n : Nat} {left right : Partition n × Fin n} →
      delete left ≡ delete right → left ≡ right

    mappedDeleteForward :
      {n : Nat} {residual : Residual n} →
      residual ∈
        map delete
          (Mark.markEnumeration {n = n} (partitionEnumeration n)) →
      residual ∈ residualEnumeration n

    mappedDeleteBackward :
      {n : Nat} {residual : Residual n} →
      residual ∈ residualEnumeration n →
      residual ∈
        map delete
          (Mark.markEnumeration {n = n} (partitionEnumeration n))

    -- A marked unit has weight one.  The residual coordinate supplied by the
    -- deletion map must preserve that unit mass.
    deletionUnitWeight :
      {n : Nat} (marked : Partition n × Fin n) →
      1 ≡ residualWeight (delete marked)

open CanonicalPartitionDeletionData public

------------------------------------------------------------------------
-- Partition count is definitionally the length of the concrete enumeration.

partitionCount : CanonicalPartitionDeletionData → Nat → Nat
partitionCount dataSet n =
  Reindex.listLength (partitionEnumeration dataSet n)

------------------------------------------------------------------------
-- Canonical adapter into the generic deletion-fibre theorem.

canonicalDeletionFibreSystem :
  CanonicalPartitionDeletionData →
  DoubleCount.ErdosDeletionFibreSystem
canonicalDeletionFibreSystem dataSet = record
  { PartitionCount = partitionCount dataSet
  ; Marked = λ n → Partition dataSet n × Fin n
  ; Residual = Residual dataSet
  ; markedEnumeration = λ n →
      Mark.markEnumeration {n = n} (partitionEnumeration dataSet n)
  ; residualEnumeration = residualEnumeration dataSet
  ; delete = delete dataSet
  ; markedWeight = λ _ → 1
  ; residualWeight = residualWeight dataSet
  ; markedUnique = markedEnumerationUnique dataSet
  ; residualUnique = residualEnumerationUnique dataSet
  ; deleteInjective = deleteInjective dataSet
  ; mappedDeleteForward = mappedDeleteForward dataSet
  ; mappedDeleteBackward = mappedDeleteBackward dataSet
  ; deletePreservesWeight = deletionUnitWeight dataSet
  ; markedFoldEvaluation = λ n →
      Mark.markedUnitFoldIsNCount
        (partitionEnumeration dataSet n)
  }

------------------------------------------------------------------------
-- Therefore n*p(n) = the residual weighted fold for every n immediately.

canonicalErdosResidualIdentity :
  (dataSet : CanonicalPartitionDeletionData) →
  (n : Nat) →
  n * partitionCount dataSet n
  ≡ DoubleCount.ErdosResidualDoubleSum
      (canonicalDeletionFibreSystem dataSet) n
canonicalErdosResidualIdentity dataSet =
  DoubleCount.erdosIdentityFromDeletionFibre
    (canonicalDeletionFibreSystem dataSet)

------------------------------------------------------------------------
-- Only the partition-specific deletion/grouping theorem remains: identify the
-- concrete residual carrier with tuples (v,k,mu), where mu is a partition of
-- n-kv, and group unit residuals into v copies for each (v,k,mu).
------------------------------------------------------------------------
