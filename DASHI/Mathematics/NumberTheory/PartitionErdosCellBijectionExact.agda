module DASHI.Mathematics.NumberTheory.PartitionErdosCellBijectionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- CONCRETE BIJECTION CARRIER
--
-- A unit mark in a partition is represented by an actual multiplicity cell
--
--   (lambda , v , j , u)
--
-- with j : Fin(m_v) selecting one occurrence of part v and u : Fin(v)
-- selecting one unit inside that part.  The deletion parameter is k=j+1.
-- Thus each partition contributes sum_v m_v*v cells, exactly its mass n.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Fin.Base using (Fin; toℕ; fromℕ<)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Mathematics.NumberTheory.FiniteNatVectorCoordinateUpdateExact as Update
import DASHI.Mathematics.NumberTheory.FiniteVectorPrefixSplitExact as Split
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityDeletionMassExact as Mass
import DASHI.Mathematics.NumberTheory.PartitionAmbientMultiplicityDeletionExact as Ambient
import DASHI.Mathematics.NumberTheory.PartitionAmbientMultiplicityNormalizationExact as Normalize

------------------------------------------------------------------------
-- Source unit cell.

record PartitionCell {n : Nat}
    (partition : Partition.MultiplicityPartition n) : Set where
  constructor partitionCell
  field
    partIndex : Fin n
    occurrence :
      Fin
        (Partition.lookupMultiplicity partIndex
          (Partition.multiplicities partition))
    unit : Fin (Partition.partValue partIndex)

open PartitionCell public

cellCopies :
  ∀ {n : Nat} {partition : Partition.MultiplicityPartition n} →
  PartitionCell partition → Nat
cellCopies cell = suc (toℕ (occurrence cell))

cellCopiesPositive :
  ∀ {n : Nat} {partition : Partition.MultiplicityPartition n}
    (cell : PartitionCell partition) →
  suc zero ≤ cellCopies cell
cellCopiesPositive cell = s≤s z≤n

cellCopiesAvailable :
  ∀ {n : Nat} {partition : Partition.MultiplicityPartition n}
    (cell : PartitionCell partition) →
  cellCopies cell ≤
    Partition.lookupMultiplicity
      (partIndex cell) (Partition.multiplicities partition)
cellCopiesAvailable cell = FinP.toℕ<n (occurrence cell)

cellDeletionChoice :
  ∀ {n : Nat} {partition : Partition.MultiplicityPartition n} →
  PartitionCell partition → Partition.PositiveDeletionChoice partition
cellDeletionChoice cell = record
  { partIndex = partIndex cell
  ; copies = cellCopies cell
  ; copiesPositive = cellCopiesPositive cell
  ; copiesAvailable = cellCopiesAvailable cell
  }

------------------------------------------------------------------------
-- Forward map: literal cell -> canonical residual quadruple.

cellToAmbientResidual :
  ∀ {n : Nat}
    {partition : Partition.MultiplicityPartition n} →
  PartitionCell partition → Ambient.ErdosAmbientResidual n
cellToAmbientResidual {partition = partition} cell =
  Ambient.deleteChoiceToAmbientResidual
    partition
    (cellDeletionChoice cell)
    (unit cell)

cellToResidual :
  ∀ {n : Nat}
    {partition : Partition.MultiplicityPartition n} →
  PartitionCell partition → Partition.ErdosMultiplicityResidual n
cellToResidual cell =
  Normalize.ambientResidualToCanonical (cellToAmbientResidual cell)

------------------------------------------------------------------------
-- Canonical residual -> padded ambient residual.
--
-- The residual decomposition r + k*v = n supplies exactly the zero-tail length
-- needed to embed the canonical Vec Nat r back into the source dimension.

weightedMassAppendZero :
  ∀ {dimension : Nat}
    (first : Nat)
    (vector : Vec Nat dimension)
    (extra : Nat) →
  Partition.weightedMassFrom first
    (Split.appendVec vector (Split.zeroVec extra))
  ≡ Partition.weightedMassFrom first vector
weightedMassAppendZero first Data.Vec.Base.[] extra =
  Normalize.weightedMassFromZeroVec first extra
weightedMassAppendZero first (x Data.Vec.Base.∷ xs) extra =
  cong (first * x +_)
    (weightedMassAppendZero (suc first) xs extra)

canonicalResidualPadded :
  ∀ {n : Nat}
    (residual : Partition.ErdosMultiplicityResidual n) →
  Ambient.AmbientMultiplicityPartition
    (Partition.residualMass residual
      + Partition.copies residual * Partition.partValue (Partition.partIndex residual))
    (Partition.residualMass residual)
canonicalResidualPadded residual =
  Ambient.ambientMultiplicityPartition padded paddedMass
  where
  canonical : Partition.MultiplicityPartition (Partition.residualMass residual)
  canonical = Partition.residualPartition residual

  extra : Nat
  extra = Partition.copies residual * Partition.partValue (Partition.partIndex residual)

  padded : Vec Nat (Partition.residualMass residual + extra)
  padded =
    Split.appendVec (Partition.multiplicities canonical) (Split.zeroVec extra)

  paddedMass :
    Partition.weightedMass padded ≡ Partition.residualMass residual
  paddedMass =
    trans
      (weightedMassAppendZero 1 (Partition.multiplicities canonical) extra)
      (Partition.massExact canonical)

canonicalResidualToAmbient :
  ∀ {n : Nat} →
  Partition.ErdosMultiplicityResidual n → Ambient.ErdosAmbientResidual n
canonicalResidualToAmbient residual =
  Ambient.erdosAmbientResidual
    (Partition.partIndex residual)
    (Partition.copies residual)
    (Partition.copiesPositive residual)
    (Partition.residualMass residual)
    ambientInN
    (Partition.decompositionExact residual)
    (Partition.unit residual)
  where
  padded = canonicalResidualPadded residual

  vectorInN : Vec Nat _
  vectorInN =
    Normalize.transportVectorToDecomposition
      (sym (Partition.decompositionExact residual))
      (Ambient.ambientMultiplicities padded)

  ambientInN :
    Ambient.AmbientMultiplicityPartition _ (Partition.residualMass residual)
  ambientInN =
    Ambient.ambientMultiplicityPartition
      vectorInN
      (trans
        (Normalize.transportWeightedMass
          (sym (Partition.decompositionExact residual))
          (Ambient.ambientMultiplicities padded))
        (Ambient.ambientMassExact padded))

------------------------------------------------------------------------
-- Reconstruct the source partition by inserting k copies.

residualSourcePartition :
  ∀ {n : Nat} →
  Partition.ErdosMultiplicityResidual n → Partition.MultiplicityPartition n
residualSourcePartition residual =
  Ambient.reconstructPartitionFromAmbient
    (canonicalResidualToAmbient residual)

------------------------------------------------------------------------
-- The source multiplicity at v contains at least the k inserted copies.

residualCopiesAvailableInSource :
  ∀ {n : Nat}
    (residual : Partition.ErdosMultiplicityResidual n) →
  Partition.copies residual ≤
    Partition.lookupMultiplicity
      (Partition.partIndex residual)
      (Partition.multiplicities (residualSourcePartition residual))
residualCopiesAvailableInSource residual =
  subst
    (λ value → Partition.copies residual ≤ value)
    (sym
      (Update.lookupAddAt
        (Partition.copies residual)
        (Partition.partIndex residual)
        (Ambient.ambientMultiplicities
          (Ambient.residualPartition (canonicalResidualToAmbient residual)))))
    (NatP.≤-trans
      (NatP.m≤m+n
        (Partition.copies residual)
        (Update.lookupNat
          (Partition.partIndex residual)
          (Ambient.ambientMultiplicities
            (Ambient.residualPartition (canonicalResidualToAmbient residual)))))
      (NatP.≤-reflexive
        (NatP.+-comm
          (Partition.copies residual)
          (Update.lookupNat
            (Partition.partIndex residual)
            (Ambient.ambientMultiplicities
              (Ambient.residualPartition (canonicalResidualToAmbient residual)))))))

------------------------------------------------------------------------
-- Positive k gives the occurrence index k-1 in the reconstructed source.

record ResidualSourceCell {n : Nat}
    (residual : Partition.ErdosMultiplicityResidual n) : Set where
  constructor residualSourceCell
  field
    source : Partition.MultiplicityPartition n
    cell : PartitionCell source
    sameSource :
      Partition.multiplicities source
      ≡ Partition.multiplicities (residualSourcePartition residual)

open ResidualSourceCell public

residualToSourceCell :
  ∀ {n : Nat}
    (residual : Partition.ErdosMultiplicityResidual n) →
  ResidualSourceCell residual
residualToSourceCell residual with Partition.copies residual
... | zero with Partition.copiesPositive residual
...   | ()
... | suc predecessor =
  residualSourceCell sourcePartition sourceCell refl
  where
  sourcePartition : Partition.MultiplicityPartition _
  sourcePartition = residualSourcePartition residual

  occurrenceBound :
    suc predecessor ≤
      Partition.lookupMultiplicity
        (Partition.partIndex residual)
        (Partition.multiplicities sourcePartition)
  occurrenceBound = residualCopiesAvailableInSource residual

  sourceCell : PartitionCell sourcePartition
  sourceCell =
    partitionCell
      (Partition.partIndex residual)
      (fromℕ< occurrenceBound)
      (Partition.unit residual)

------------------------------------------------------------------------
-- Forward and reverse maps are now concrete.  The remaining theorem is their
-- exact residual/cell round-trip after canonical padding/normalization; once
-- proved, the finite enumeration permutation follows from existing generic
-- reindexing machinery.
------------------------------------------------------------------------
