module DASHI.Mathematics.NumberTheory.PartitionErdosFiniteKeyEnumerationExact where

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
-- Following the exact-shell enumeration pattern, semantic identity is carried
-- by finite coordinates, not by proof witnesses.  Following the ITIR key/
-- correspondence lanes, uniqueness is explicit and ambiguity is not silently
-- resolved by proof erasure.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.List.Base using (allFin)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-allFin)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as UniqueP
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec)

import DASHI.Mathematics.NumberTheory.FiniteDependentPairEnumerationExact as Dep
import DASHI.Mathematics.NumberTheory.FiniteNatVectorCoordinateUpdateExact as Update
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityEnumerationExact as Enumeration

------------------------------------------------------------------------
-- Proof-free marked cell key.
--
-- The occurrence and unit bounds are data: Fin(m_v) and Fin(v).  There is no
-- mass equality, positivity proof, availability proof, or decomposition proof
-- inside the key identity.

CellKey : Nat → Set
CellKey n =
  Σ (Vec Nat n) λ vector →
  Σ (Fin n) λ index →
  Σ (Fin (Partition.lookupMultiplicity index vector)) λ occurrence →
  Fin (Partition.partValue index)

ResidualKey : Nat → Set
ResidualKey n =
  Σ (Vec Nat n) λ residualVector →
  Σ (Fin n) λ index →
  Nat × Fin (Partition.partValue index)

cellVector : ∀ {n} → CellKey n → Vec Nat n
cellVector = proj₁

cellIndex : ∀ {n} → CellKey n → Fin n
cellIndex key = proj₁ (proj₂ key)

cellOccurrence :
  ∀ {n} (key : CellKey n) →
  Fin (Partition.lookupMultiplicity (cellIndex key) (cellVector key))
cellOccurrence key = proj₁ (proj₂ (proj₂ key))

cellUnit :
  ∀ {n} (key : CellKey n) → Fin (Partition.partValue (cellIndex key))
cellUnit key = proj₂ (proj₂ (proj₂ key))

cellCopies : ∀ {n} → CellKey n → Nat
cellCopies key = suc (toℕ (cellOccurrence key))

------------------------------------------------------------------------
-- Canonical nested finite enumeration.

occurrenceUnitEnumeration :
  ∀ {n} (vector : Vec Nat n) (index : Fin n) →
  List
    (Σ (Fin (Partition.lookupMultiplicity index vector)) λ occurrence →
      Fin (Partition.partValue index))
occurrenceUnitEnumeration vector index =
  Dep.dependentPairs
    (allFin (Partition.lookupMultiplicity index vector))
    (λ _ → allFin (Partition.partValue index))

partCellEnumeration :
  ∀ {n} (vector : Vec Nat n) →
  List
    (Σ (Fin n) λ index →
      Σ (Fin (Partition.lookupMultiplicity index vector)) λ occurrence →
      Fin (Partition.partValue index))
partCellEnumeration {n} vector =
  Dep.dependentPairs
    (allFin n)
    (occurrenceUnitEnumeration vector)

cellKeyEnumeration : (n : Nat) → List (CellKey n)
cellKeyEnumeration n =
  Dep.dependentPairs
    (Enumeration.partitionMultiplicityVectors n)
    partCellEnumeration

------------------------------------------------------------------------
-- Duplicate-freedom is inherited compositionally from the canonical partition
-- vector list and stdlib `allFin` fibres.

occurrenceUnitUnique :
  ∀ {n} (vector : Vec Nat n) (index : Fin n) →
  Unique (occurrenceUnitEnumeration vector index)
occurrenceUnitUnique vector index =
  Dep.dependentPairsUnique
    (λ _ → allFin (Partition.partValue index))
    (UniqueP.allFin⁺ (Partition.lookupMultiplicity index vector))
    (λ _ → UniqueP.allFin⁺ (Partition.partValue index))

partCellUnique :
  ∀ {n} (vector : Vec Nat n) →
  Unique (partCellEnumeration vector)
partCellUnique {n} vector =
  Dep.dependentPairsUnique
    (occurrenceUnitEnumeration vector)
    (UniqueP.allFin⁺ n)
    (occurrenceUnitUnique vector)

cellKeyEnumerationUnique :
  (n : Nat) → Unique (cellKeyEnumeration n)
cellKeyEnumerationUnique n =
  Dep.dependentPairsUnique
    partCellEnumeration
    (Enumeration.partitionMultiplicityVectorsUnique n)
    partCellUnique

------------------------------------------------------------------------
-- Completeness for every key whose source vector is in the canonical partition
-- enumeration.

cellKeyListed :
  ∀ {n} (key : CellKey n) →
  cellVector key ∈ Enumeration.partitionMultiplicityVectors n →
  key ∈ cellKeyEnumeration n
cellKeyListed (vector , index , occurrence , unit) vectorMember =
  Dep.dependentPairsMember partCellEnumeration
    vectorMember
    (Dep.dependentPairsMember
      (occurrenceUnitEnumeration vector)
      (∈-allFin index)
      (Dep.dependentPairsMember
        (λ _ → allFin (Partition.partValue index))
        (∈-allFin occurrence)
        (∈-allFin unit)))

------------------------------------------------------------------------
-- Deletion normal form.  Store the occurrence predecessor j literally; the
-- deleted multiplicity is k=j+1.  ResidualKey is intentionally not required to
-- be finite as a type.  Its canonical enumeration will be the finite image of
-- `cellKeyEnumeration`.

deleteKey : ∀ {n} → CellKey n → ResidualKey n
deleteKey key =
  Update.subtractAt (cellCopies key) (cellIndex key) (cellVector key)
  , cellIndex key
  , toℕ (cellOccurrence key)
  , cellUnit key

residualVector : ∀ {n} → ResidualKey n → Vec Nat n
residualVector = proj₁

residualIndex : ∀ {n} → ResidualKey n → Fin n
residualIndex residual = proj₁ (proj₂ residual)

residualPredecessor : ∀ {n} → ResidualKey n → Nat
residualPredecessor residual = proj₁ (proj₂ (proj₂ residual))

residualUnit :
  ∀ {n} (residual : ResidualKey n) →
  Fin (Partition.partValue (residualIndex residual))
residualUnit residual = proj₂ (proj₂ (proj₂ residual))

residualCopies : ∀ {n} → ResidualKey n → Nat
residualCopies residual = suc (residualPredecessor residual)

------------------------------------------------------------------------
-- No proof-bearing partition record appears in either key type.
------------------------------------------------------------------------
