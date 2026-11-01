module DASHI.Mathematics.NumberTheory.PartitionGradedPointingInstanceExact where

------------------------------------------------------------------------
-- PARTITIONS AS A GRADED MULTIPLICITY POINTING SYSTEM
--
-- This module identifies the multiplicity-vector partition carrier with the
-- generic GradedMultiplicityPointingResidualExact abstraction.  The resulting
-- generic pointed cell is exactly the data already used by the Erdos deletion
-- construction: part coordinate, occurrence, and unit inside the part.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Fin.Base using (Fin)
  renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.NumberTheory.FiniteProductEnumerationExact as Product
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex
import DASHI.Mathematics.NumberTheory.GradedMultiplicityPointingResidualExact as Pointing
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.PartitionAmbientMultiplicityNormalizationExact as Normalize
import DASHI.Mathematics.NumberTheory.PartitionErdosCellBijectionExact as ErdosCell

------------------------------------------------------------------------
-- Fold of coordinate weight * multiplicity over all Fin coordinates is the
-- recursive weightedMassFrom definition.

weightedGeneratorFoldFrom :
  ∀ {n : Nat}
    (first : Nat)
    (vector : Vec Nat n) →
  Reindex.foldNat
    (λ index →
      Partition.coordinateWeightFrom first index
      * Partition.lookupMultiplicity index vector)
    (Product.allFin n)
  ≡ Partition.weightedMassFrom first vector
weightedGeneratorFoldFrom first [] = refl
weightedGeneratorFoldFrom first (multiplicity ∷ rest) =
  trans
    (cong
      (first * multiplicity +_)
      (Reindex.foldMap
        (λ index →
          Partition.coordinateWeightFrom first index
          * Partition.lookupMultiplicity index (multiplicity ∷ rest))
        fsuc
        (Product.allFin _)))
    (cong
      (first * multiplicity +_)
      (weightedGeneratorFoldFrom (suc first) rest))

partitionWeightedGeneratorFold :
  ∀ {n : Nat}
    (partition : Partition.MultiplicityPartition n) →
  Reindex.foldNat
    (λ index →
      Partition.partValue index
      * Partition.lookupMultiplicity index (Partition.multiplicities partition))
    (Product.allFin n)
  ≡ n
partitionWeightedGeneratorFold partition =
  trans
    (Reindex.foldPointwise
      (λ index →
        Partition.partValue index
        * Partition.lookupMultiplicity index (Partition.multiplicities partition))
      (λ index →
        Partition.coordinateWeightFrom 1 index
        * Partition.lookupMultiplicity index (Partition.multiplicities partition))
      (Product.allFin _)
      (λ index →
        cong
          (_* Partition.lookupMultiplicity index (Partition.multiplicities partition))
          (sym (Normalize.coordinateWeightOneIsPartValue index))))
    (trans
      (weightedGeneratorFoldFrom 1 (Partition.multiplicities partition))
      (Partition.massExact partition))

------------------------------------------------------------------------
-- Canonical generic system attached to one partition.

partitionPointingSystem :
  ∀ {n : Nat} →
  Partition.MultiplicityPartition n → Pointing.GradedMultiplicitySystem
partitionPointingSystem {n} partition = record
  { Generator = Fin n
  ; generators = Product.allFin n
  ; multiplicity =
      λ index →
        Partition.lookupMultiplicity index (Partition.multiplicities partition)
  ; weight = Partition.partValue
  ; grade = n
  ; gradeExact = partitionWeightedGeneratorFold partition
  }

partitionPointedCellsHaveGrade :
  ∀ {n : Nat}
    (partition : Partition.MultiplicityPartition n) →
  Reindex.listLength
    (Pointing.pointedCells (partitionPointingSystem partition))
  ≡ n
partitionPointedCellsHaveGrade partition =
  Pointing.pointedCellsLengthEqualsGrade (partitionPointingSystem partition)

------------------------------------------------------------------------
-- Generic pointed cells and the concrete Erdos PartitionCell are the same
-- information.  Keep explicit conversion functions rather than relying on
-- record/Sigma definitional coincidence across theorem owners.

genericCellToPartitionCell :
  ∀ {n : Nat} {partition : Partition.MultiplicityPartition n} →
  Pointing.PointedCell (partitionPointingSystem partition) →
  ErdosCell.PartitionCell partition
genericCellToPartitionCell (index , occurrence , unit) =
  ErdosCell.partitionCell index occurrence unit

partitionCellToGenericCell :
  ∀ {n : Nat} {partition : Partition.MultiplicityPartition n} →
  ErdosCell.PartitionCell partition →
  Pointing.PointedCell (partitionPointingSystem partition)
partitionCellToGenericCell cell =
  ErdosCell.partIndex cell , ErdosCell.occurrence cell , ErdosCell.unit cell

genericPartitionCellRoundTrip :
  ∀ {n : Nat} {partition : Partition.MultiplicityPartition n}
    (cell : Pointing.PointedCell (partitionPointingSystem partition)) →
  partitionCellToGenericCell (genericCellToPartitionCell cell) ≡ cell
genericPartitionCellRoundTrip (index , occurrence , unit) = refl

partitionGenericCellRoundTrip :
  ∀ {n : Nat} {partition : Partition.MultiplicityPartition n}
    (cell : ErdosCell.PartitionCell partition) →
  genericCellToPartitionCell (partitionCellToGenericCell cell) ≡ cell
partitionGenericCellRoundTrip (ErdosCell.partitionCell index occurrence unit) = refl

------------------------------------------------------------------------
-- This is the exact partition/Fock-style grading interface: total grade is
-- literally the finite cardinality of generator-occurrence-unit cells.
------------------------------------------------------------------------
