module DASHI.Mathematics.NumberTheory.PartitionAmbientMultiplicityDeletionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- P. Erdos,
-- "On an Elementary Proof of Some Asymptotic Formulas in the Theory of
-- Partitions", Annals of Mathematics (2) 43 (1942), 437--450.
-- DOI: 10.2307/1968802.
--
-- REPRESENTATION BOUNDARY
--
-- A canonical MultiplicityPartition r uses Vec Nat r.  Deleting mass from a
-- grade-n vector leaves a Vec Nat n, so it must not silently be cast to the
-- canonical residual carrier.  This module introduces an ambient carrier with
-- independent vector dimension and exact mass, performs deletion there, and
-- proves exact vector-level reconstruction.  Canonical truncation is a later
-- explicit normalization theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (_≤_)
open import Data.Vec.Base using (Vec)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.NumberTheory.FiniteNatVectorCoordinateUpdateExact as Update
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.PartitionMultiplicityDeletionMassExact as Mass

------------------------------------------------------------------------
-- Ambient finite multiplicity carrier.

record AmbientMultiplicityPartition
    (dimension mass : Nat) : Set where
  constructor ambientMultiplicityPartition
  field
    ambientMultiplicities : Vec Nat dimension
    ambientMassExact : Partition.weightedMass ambientMultiplicities ≡ mass

open AmbientMultiplicityPartition public

canonicalToAmbient :
  ∀ {n : Nat} →
  Partition.MultiplicityPartition n →
  AmbientMultiplicityPartition n n
canonicalToAmbient partition =
  ambientMultiplicityPartition
    (Partition.multiplicities partition)
    (Partition.massExact partition)

------------------------------------------------------------------------
-- Literal residual produced by deleting k copies at coordinate v.

record ErdosAmbientResidual (n : Nat) : Set where
  constructor erdosAmbientResidual
  field
    partIndex : Fin n
    copies : Nat
    copiesPositive : suc 0 ≤ copies
    residualMass : Nat
    residualPartition : AmbientMultiplicityPartition n residualMass
    decompositionExact :
      residualMass + copies * Partition.partValue partIndex ≡ n
    unit : Fin (Partition.partValue partIndex)

open ErdosAmbientResidual public

deleteChoiceToAmbientResidual :
  ∀ {n : Nat}
    (partition : Partition.MultiplicityPartition n)
    (choice : Partition.PositiveDeletionChoice partition) →
  Fin (Partition.partValue (Partition.PositiveDeletionChoice.partIndex choice)) →
  ErdosAmbientResidual n
deleteChoiceToAmbientResidual partition choice unitLabel =
  erdosAmbientResidual
    index
    amount
    (Partition.PositiveDeletionChoice.copiesPositive choice)
    residualMassValue
    (ambientMultiplicityPartition residualVector refl)
    (Mass.partitionDeletionMass partition amount index available)
    unitLabel
  where
  index : Fin _
  index = Partition.PositiveDeletionChoice.partIndex choice

  amount : Nat
  amount = Partition.PositiveDeletionChoice.copies choice

  available :
    amount ≤
      Partition.lookupMultiplicity index (Partition.multiplicities partition)
  available = Partition.PositiveDeletionChoice.copiesAvailable choice

  residualVector : Vec Nat _
  residualVector =
    Update.subtractAt amount index (Partition.multiplicities partition)

  residualMassValue : Nat
  residualMassValue = Partition.weightedMass residualVector

------------------------------------------------------------------------
-- Reconstruction by re-inserting the deleted multiplicity.

reconstructPartitionFromAmbient :
  ∀ {n : Nat} →
  ErdosAmbientResidual n →
  Partition.MultiplicityPartition n
reconstructPartitionFromAmbient residual =
  Partition.multiplicityPartition sourceVector sourceMassExact
  where
  index : Fin _
  index = partIndex residual

  amount : Nat
  amount = copies residual

  residualVector : Vec Nat _
  residualVector =
    ambientMultiplicities (residualPartition residual)

  sourceVector : Vec Nat _
  sourceVector = Update.addAt amount index residualVector

  insertedMass :
    Partition.weightedMass sourceVector
    ≡ Partition.weightedMass residualVector
      + amount * Partition.partValue index
  insertedMass = Mass.partitionInsertionMass residualVector amount index

  residualMassRewrite :
    Partition.weightedMass residualVector
      + amount * Partition.partValue index
    ≡ residualMass residual + amount * Partition.partValue index
  residualMassRewrite =
    cong
      (_+ amount * Partition.partValue index)
      (ambientMassExact (residualPartition residual))

  sourceMassExact : Partition.weightedMass sourceVector ≡ n
  sourceMassExact =
    trans insertedMass
      (trans residualMassRewrite (decompositionExact residual))

------------------------------------------------------------------------
-- Vector-level inverse laws.  These deliberately avoid equality of dependent
-- proof fields; the finite multiplicity data are recovered exactly.

reconstructedDeletionReturnsAmbientVector :
  ∀ {n : Nat}
    (residual : ErdosAmbientResidual n) →
  Update.subtractAt
    (copies residual)
    (partIndex residual)
    (Partition.multiplicities (reconstructPartitionFromAmbient residual))
  ≡ ambientMultiplicities (residualPartition residual)
reconstructedDeletionReturnsAmbientVector residual =
  Update.subtractAfterAddAt
    (copies residual)
    (partIndex residual)
    (ambientMultiplicities (residualPartition residual))

reconstructDeletedPartitionVector :
  ∀ {n : Nat}
    (partition : Partition.MultiplicityPartition n)
    (choice : Partition.PositiveDeletionChoice partition)
    (unitLabel :
      Fin (Partition.partValue
        (Partition.PositiveDeletionChoice.partIndex choice))) →
  Partition.multiplicities
    (reconstructPartitionFromAmbient
      (deleteChoiceToAmbientResidual partition choice unitLabel))
  ≡ Partition.multiplicities partition
reconstructDeletedPartitionVector partition choice unitLabel =
  Update.addAfterSubtractAt
    (Partition.PositiveDeletionChoice.copies choice)
    (Partition.PositiveDeletionChoice.partIndex choice)
    (Partition.multiplicities partition)
    (Partition.PositiveDeletionChoice.copiesAvailable choice)

------------------------------------------------------------------------
-- The remaining normalization theorem is now sharply typed:
--
--   AmbientMultiplicityPartition n r  ->  MultiplicityPartition r
--
-- for the residuals generated here (or, more generally, when all coordinates
-- above r are proved zero).  No such cast is assumed in this module.
------------------------------------------------------------------------
