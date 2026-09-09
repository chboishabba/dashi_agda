{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5DiagonalFiniteVolumeSameObjectExact where

------------------------------------------------------------------------
-- DIAGONAL MEASURE = THE SELECTED PHYSICAL FINITE-VOLUME MEASURE
--
-- PhysicalExpectationProducerData historically stores
-- `diagonalMeasureDefinition : forall cutoff -> Set`.  That receipt cannot be
-- used to transport a theorem proved on the physical finite-volume measure
-- family onto the selected diagonal sequence.  The exact same-object theorem
-- required for such transport is isolated here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5

record DiagonalFiniteVolumeSameObject
    {Measure Observable Scalar : Set}
    (producer : T5.PhysicalExpectationProducerData Measure Observable Scalar)
    : Set₁ where
  field
    diagonalMeasureIsSelectedFiniteVolume : ∀ cutoff →
      T5.diagonalMeasure producer cutoff
      ≡ T5.finiteVolumeMeasure (T5.thermodynamic producer) cutoff
          (T5.diagonalVolume (T5.thermodynamic producer) cutoff)

open DiagonalFiniteVolumeSameObject public

-- Once the measure equality is inhabited, every observable expectation may be
-- transported with no new analytic theorem.
diagonalExpectationIsSelectedFiniteVolumeExpectation :
  ∀ {Measure Observable Scalar}
    {producer : T5.PhysicalExpectationProducerData Measure Observable Scalar} →
  DiagonalFiniteVolumeSameObject producer →
  ∀ cutoff observable →
  Gram.expectation
      (T5.operations (T5.thermodynamic producer))
      (T5.diagonalMeasure producer cutoff)
      observable
  ≡
  Gram.expectation
      (T5.operations (T5.thermodynamic producer))
      (T5.finiteVolumeMeasure (T5.thermodynamic producer) cutoff
        (T5.diagonalVolume (T5.thermodynamic producer) cutoff))
      observable
diagonalExpectationIsSelectedFiniteVolumeExpectation sameObject cutoff observable =
  cong
    (λ measure →
      Gram.expectation
        (T5.operations (T5.thermodynamic _)) measure observable)
    (diagonalMeasureIsSelectedFiniteVolume sameObject cutoff)

-- The transport compiler is structural; the physical equality itself remains
-- the first missing theorem until an exact producer is found.
diagonalFiniteVolumeExpectationTransportLevel : ProofLevel
diagonalFiniteVolumeExpectationTransportLevel = machineChecked

physicalDiagonalFiniteVolumeSameObjectLevel : ProofLevel
physicalDiagonalFiniteVolumeSameObjectLevel = conditional
