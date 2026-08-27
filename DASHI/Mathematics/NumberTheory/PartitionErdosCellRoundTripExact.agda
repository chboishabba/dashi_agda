module DASHI.Mathematics.NumberTheory.PartitionErdosCellRoundTripExact where

------------------------------------------------------------------------
-- ERDOS CELL / RESIDUAL ROUND-TRIP SUPPORT
--
-- This module closes the representation-sensitive part of the concrete
-- pointing/deletion bijection.  Normalizing an ambient exact-mass residual and
-- padding it back with its forced zero tail recovers the ambient multiplicity
-- vector exactly.  Consequently cell deletion followed by canonical residual
-- reconstruction recovers the original source multiplicity vector.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.NumberTheory.FiniteNatVectorCoordinateUpdateExact as Update
import DASHI.Mathematics.NumberTheory.FiniteVectorPrefixSplitExact as Split
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.PartitionAmbientMultiplicityDeletionExact as Ambient
import DASHI.Mathematics.NumberTheory.PartitionAmbientMultiplicityNormalizationExact as Normalize
import DASHI.Mathematics.NumberTheory.PartitionErdosCellBijectionExact as Cell

------------------------------------------------------------------------
-- Normalize then pad: exact ambient vector recovery.

normalizeThenPadVector :
  ∀ {mass extra : Nat}
    (ambient : Ambient.AmbientMultiplicityPartition (mass + extra) mass) →
  Split.appendVec
    (Partition.multiplicities (Normalize.normalizeAmbient ambient))
    (Split.zeroVec extra)
  ≡ Ambient.ambientMultiplicities ambient
normalizeThenPadVector {mass} {extra} ambient =
  trans
    (cong
      (Split.appendVec
        (Split.takePrefix mass extra (Ambient.ambientMultiplicities ambient)))
      (sym (Normalize.ambientTailZero ambient)))
    (Split.splitReconstruct mass extra (Ambient.ambientMultiplicities ambient))

------------------------------------------------------------------------
-- Transport along a length equality and back is literal identity.

transportVectorRoundTrip :
  ∀ {left right : Nat}
    (equality : left ≡ right)
    (vector : Vec Nat right) →
  Normalize.transportVectorToDecomposition (sym equality)
    (Normalize.transportVectorToDecomposition equality vector)
  ≡ vector
transportVectorRoundTrip refl vector = refl

------------------------------------------------------------------------
-- Canonicalize an ambient residual, pad it, and transport back to the source
-- dimension: the original ambient residual vector is recovered exactly.

canonicalRoundTripAmbientVector :
  ∀ {n : Nat}
    (residual : Ambient.ErdosAmbientResidual n) →
  Ambient.ambientMultiplicities
    (Ambient.residualPartition
      (Cell.canonicalResidualToAmbient
        (Normalize.ambientResidualToCanonical residual)))
  ≡ Ambient.ambientMultiplicities (Ambient.residualPartition residual)
canonicalRoundTripAmbientVector residual =
  trans
    (cong
      (Normalize.transportVectorToDecomposition
        (sym (Ambient.decompositionExact residual)))
      (normalizeThenPadVector
        (Normalize.ambientResidualInDecomposedDimension residual)))
    (transportVectorRoundTrip
      (Ambient.decompositionExact residual)
      (Ambient.ambientMultiplicities (Ambient.residualPartition residual)))

------------------------------------------------------------------------
-- Concrete forward/reverse source-data round trip.

cellResidualSourceVectorRoundTrip :
  ∀ {n : Nat}
    {partition : Partition.MultiplicityPartition n}
    (cell : Cell.PartitionCell partition) →
  Partition.multiplicities
    (Cell.residualSourcePartition (Cell.cellToResidual cell))
  ≡ Partition.multiplicities partition
cellResidualSourceVectorRoundTrip {partition = partition} cell =
  trans
    (cong
      (Update.addAt
        (Cell.cellCopies cell)
        (Cell.partIndex cell))
      (canonicalRoundTripAmbientVector (Cell.cellToAmbientResidual cell)))
    (Ambient.reconstructDeletedPartitionVector
      partition
      (Cell.cellDeletionChoice cell)
      (Cell.unit cell))

------------------------------------------------------------------------
-- The theorem is intentionally extensional on multiplicity data.  Equality of
-- dependent proof fields is not required for finite counting or reindexing.
------------------------------------------------------------------------
