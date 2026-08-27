module DASHI.Mathematics.NumberTheory.PartitionErdosGradedFamilyInstanceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- PURPOSE
-- Instantiate the generic whole-family pointing/residual interface without
-- requiring proof irrelevance.  Pointed objects and residuals are compared by
-- their finite mathematical data, not by equality of attached proof fields.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (toℕ)
import Data.Fin.Properties as FinP
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.NumberTheory.GradedFamilyPointingResidualExact as Family
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.PartitionAmbientMultiplicityDeletionExact as Ambient
import DASHI.Mathematics.NumberTheory.PartitionErdosCellBijectionExact as Cell
import DASHI.Mathematics.NumberTheory.PartitionErdosCellRoundTripExact as Round

------------------------------------------------------------------------
-- Whole partition family and its literal Ferrers-style cells.

partitionPointingFamily : Family.GradedPointingFamily
partitionPointingFamily = record
  { Object = Partition.MultiplicityPartition
  ; Cell = Cell.PartitionCell
  }

PartitionPointed : Nat → Set
PartitionPointed n = Family.PointedObject partitionPointingFamily n

------------------------------------------------------------------------
-- Extensional pointed equality: source multiplicities plus the deletion data
-- (v,k,u).  Unit labels are compared through toℕ so their equality does not
-- depend on proof-level transport of their Fin bounds.

record PointedDataEquivalent {n : Nat}
    (left right : PartitionPointed n) : Set where
  field
    sourceMultiplicities :
      Partition.multiplicities (proj₁ left)
      ≡ Partition.multiplicities (proj₁ right)
    partIndex :
      Cell.partIndex (proj₂ left) ≡ Cell.partIndex (proj₂ right)
    copies :
      Cell.cellCopies (proj₂ left) ≡ Cell.cellCopies (proj₂ right)
    unitIndex :
      toℕ (Cell.unit (proj₂ left)) ≡ toℕ (Cell.unit (proj₂ right))

open PointedDataEquivalent public

pointedDataReflexive :
  ∀ {n : Nat} (pointed : PartitionPointed n) →
  PointedDataEquivalent pointed pointed
pointedDataReflexive pointed = record
  { sourceMultiplicities = refl
  ; partIndex = refl
  ; copies = refl
  ; unitIndex = refl
  }

------------------------------------------------------------------------
-- Extensional residual equality.  Canonical residual vectors have varying
-- lengths, so compare their exact zero-padded ambient vectors in fixed grade n.

residualAmbientVector :
  ∀ {n : Nat} → Partition.ErdosMultiplicityResidual n →
  Data.Vec.Base.Vec Nat n
residualAmbientVector residual =
  Ambient.ambientMultiplicities
    (Ambient.residualPartition (Cell.canonicalResidualToAmbient residual))

record ResidualDataEquivalent {n : Nat}
    (left right : Partition.ErdosMultiplicityResidual n) : Set where
  field
    partIndex :
      Partition.partIndex left ≡ Partition.partIndex right
    copies :
      Partition.copies left ≡ Partition.copies right
    ambientResidual :
      residualAmbientVector left ≡ residualAmbientVector right
    unitIndex :
      toℕ (Partition.unit left) ≡ toℕ (Partition.unit right)

open ResidualDataEquivalent public

residualDataReflexive :
  ∀ {n : Nat} (residual : Partition.ErdosMultiplicityResidual n) →
  ResidualDataEquivalent residual residual
residualDataReflexive residual = record
  { partIndex = refl
  ; copies = refl
  ; ambientResidual = refl
  ; unitIndex = refl
  }

------------------------------------------------------------------------
-- Reverse map as an actual pointed grade-n object.

insertResidual :
  ∀ {n : Nat} →
  Partition.ErdosMultiplicityResidual n → PartitionPointed n
insertResidual residual with Cell.residualToSourceCell residual
... | Cell.residualSourceCell source cell same = source , cell

deletePointed :
  ∀ {n : Nat} →
  PartitionPointed n → Partition.ErdosMultiplicityResidual n
deletePointed pointed = Cell.cellToResidual (proj₂ pointed)

------------------------------------------------------------------------
-- The occurrence reconstructed from positive k has exactly k cells before it.

insertedCellCopiesExact :
  ∀ {n : Nat} (residual : Partition.ErdosMultiplicityResidual n) →
  Cell.cellCopies (proj₂ (insertResidual residual)) ≡ Partition.copies residual
insertedCellCopiesExact residual with Partition.copies residual
... | zero with Partition.copiesPositive residual
...   | ()
... | suc predecessor =
  cong suc (FinP.toℕ-fromℕ< (Cell.residualCopiesAvailableInSource residual))

------------------------------------------------------------------------
-- Deleting the reconstructed occurrence recovers the exact padded residual
-- vector.  This is the reverse direction of the representation-sensitive
-- round trip.

insertedDeletionAmbientVector :
  ∀ {n : Nat} (residual : Partition.ErdosMultiplicityResidual n) →
  Ambient.ambientMultiplicities
    (Ambient.residualPartition
      (Cell.cellToAmbientResidual (proj₂ (insertResidual residual))))
  ≡ residualAmbientVector residual
insertedDeletionAmbientVector residual with Partition.copies residual
... | zero with Partition.copiesPositive residual
...   | ()
... | suc predecessor =
  Ambient.reconstructedDeletionReturnsAmbientVector
    (Cell.canonicalResidualToAmbient residual)

------------------------------------------------------------------------
-- Residual -> pointed -> residual, modulo exactly the finite residual data.

residualDeleteInsert :
  ∀ {n : Nat} (residual : Partition.ErdosMultiplicityResidual n) →
  ResidualDataEquivalent (deletePointed (insertResidual residual)) residual
residualDeleteInsert residual = record
  { partIndex = refl
  ; copies = insertedCellCopiesExact residual
  ; ambientResidual =
      trans
        (Round.canonicalRoundTripAmbientVector
          (Cell.cellToAmbientResidual (proj₂ (insertResidual residual))))
        (insertedDeletionAmbientVector residual)
  ; unitIndex = refl
  }

------------------------------------------------------------------------
-- Pointed -> residual -> pointed, modulo source data and literal cell data.

pointedInsertDelete :
  ∀ {n : Nat} (pointed : PartitionPointed n) →
  PointedDataEquivalent (insertResidual (deletePointed pointed)) pointed
pointedInsertDelete (partition , cell) = record
  { sourceMultiplicities = Round.cellResidualSourceVectorRoundTrip cell
  ; partIndex = refl
  ; copies = insertedCellCopiesExact (Cell.cellToResidual cell)
  ; unitIndex = refl
  }

------------------------------------------------------------------------
-- Generic whole-family extensional decomposition instance.

partitionErdosFamilyDecomposition :
  Family.ExtensionalGradedFamilyResidualDecomposition partitionPointingFamily
partitionErdosFamilyDecomposition = record
  { Residual = Partition.ErdosMultiplicityResidual
  ; PointedEquivalent = PointedDataEquivalent
  ; ResidualEquivalent = ResidualDataEquivalent
  ; pointedReflexive = pointedDataReflexive
  ; residualReflexive = residualDataReflexive
  ; delete = deletePointed
  ; insert = insertResidual
  ; deleteInsert = residualDeleteInsert
  ; insertDelete = pointedInsertDelete
  }

------------------------------------------------------------------------
-- The Erdős cell/residual equivalence is therefore closed at the finite data
-- level, independently of proof equality for mass/decomposition witnesses.
------------------------------------------------------------------------
