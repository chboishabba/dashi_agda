module DASHI.Moonshine.RankOneFockMultiplicityGradingBridgeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Victor G. Kac,
-- "Vertex Algebras for Beginners", second edition, AMS, 1998.
--
-- Igor Frenkel, James Lepowsky and Arne Meurman,
-- "A natural representation of the Fischer-Griess Monster with the modular
-- function J as character", PNAS 81 (1984), 3256--3260.
-- DOI: 10.1073/pnas.81.10.3256.
--
-- PURPOSE
-- Make explicit the common finite carrier behind integer partitions and
-- rank-one bosonic occupation numbers.  A multiplicity vector m_v is read as
-- the occupation number of oscillator mode v, and the weighted partition mass
-- sum_v v*m_v is exactly the Fock grade/energy.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin)

import DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact as Partition
import DASHI.Mathematics.NumberTheory.PartitionGradedPointingInstanceExact as Pointing
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as Reindex

------------------------------------------------------------------------
-- Occupation-number presentation.

RankOneOccupationState : Nat → Set
RankOneOccupationState = Partition.MultiplicityPartition

occupationNumber :
  ∀ {n : Nat} →
  RankOneOccupationState n → Fin n → Nat
occupationNumber state index =
  Partition.lookupMultiplicity index (Partition.multiplicities state)

oscillatorModeWeight :
  ∀ {n : Nat} → Fin n → Nat
oscillatorModeWeight = Partition.partValue

occupationEnergy :
  ∀ {n : Nat} → RankOneOccupationState n → Nat
occupationEnergy state =
  Partition.weightedMass (Partition.multiplicities state)

occupationEnergyIsGrade :
  ∀ {n : Nat} (state : RankOneOccupationState n) →
  occupationEnergy state ≡ n
occupationEnergyIsGrade = Partition.massExact

------------------------------------------------------------------------
-- The grade is also the exact number of generator-occurrence-unit cells.

occupationPointedCellCountIsGrade :
  ∀ {n : Nat} (state : RankOneOccupationState n) →
  Reindex.listLength
    (DASHI.Mathematics.NumberTheory.GradedMultiplicityPointingResidualExact.pointedCells
      (Pointing.partitionPointingSystem state))
  ≡ n
occupationPointedCellCountIsGrade = Pointing.partitionPointedCellsHaveGrade

------------------------------------------------------------------------
-- Honesty boundary.
--
-- This bridge identifies the all-n occupation-number / grading carrier.  It
-- does not claim that the existing explicit `RankOneFockBasis` datatype,
-- currently constructed only through grade 5, is already bijective with this
-- all-n carrier.  That basis-extension theorem remains a separate owner.
------------------------------------------------------------------------
