{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact where

------------------------------------------------------------------------
-- PREFERRED EXPECTATION PRODUCER WITH DEFINITIONAL DIAGONAL MEASURE
--
-- Historical PhysicalExpectationProducerData leaves `diagonalMeasure` abstract
-- and records its intended finite-volume meaning only through a Set-valued
-- `diagonalMeasureDefinition`.  On the preferred Clay route this is unnecessary:
-- define the diagonal sequence literally as
--
--   finiteVolumeMeasure cutoff (diagonalVolume cutoff)
--
-- and require every downstream moment/tail witness on that same sequence.
-- The resulting diagonal/finite-volume same-object theorem is `refl`.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5

selectedFiniteVolumeSequence :
  ∀ {Measure Observable Scalar} →
  T5.PhysicalThermodynamicClusterData Measure Observable Scalar →
  Nat → Measure
selectedFiniteVolumeSequence thermodynamic cutoff =
  T5.finiteVolumeMeasure thermodynamic cutoff
    (T5.diagonalVolume thermodynamic cutoff)

record PreferredDiagonalExpectationProducerInputs
    (Measure Observable Scalar : Set)
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData Measure Observable Scalar) : Set₁ where
  field
    moments : T5.ExponentialMomentProducer
      (T5.operations thermodynamic)
      (selectedFiniteVolumeSequence thermodynamic)
      (T5.RenormalizedObservable thermodynamic)

    UniformlyIntegrable : (Nat → Observable) → Set

    witnessImpliesUniformlyIntegrable :
      ∀ {sequence : Nat → Observable} →
      T5.UniformIntegrabilityWitness Observable Scalar sequence →
      UniformlyIntegrable sequence

    boundedObservableTail : ∀ observable →
      T5.BoundedObservable thermodynamic observable →
      T5.TailControlledConvergence Scalar
        (Gram.Converges (T5.scalarConvergence thermodynamic))
        (λ cutoff →
          Gram.expectation (T5.operations thermodynamic)
            (selectedFiniteVolumeSequence thermodynamic cutoff) observable)
        (Gram.expectation (T5.operations thermodynamic)
          (T5.continuumMeasure thermodynamic) observable)

    boundedObservableHasWitness : ∀ observable →
      T5.BoundedObservable thermodynamic observable → Set

    weakConvergencePlusUniformIntegrability : ∀ sequence →
      UniformlyIntegrable sequence → Set

open PreferredDiagonalExpectationProducerInputs public

compilePreferredDiagonalExpectationProducer :
  ∀ {Measure Observable Scalar}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData Measure Observable Scalar} →
  PreferredDiagonalExpectationProducerInputs
    Measure Observable Scalar thermodynamic →
  T5.PhysicalExpectationProducerData Measure Observable Scalar
compilePreferredDiagonalExpectationProducer {thermodynamic = thermodynamic} inputs = record
  { thermodynamic = thermodynamic
  ; diagonalMeasure = selectedFiniteVolumeSequence thermodynamic
  ; diagonalMeasureDefinition = λ cutoff →
      selectedFiniteVolumeSequence thermodynamic cutoff
      ≡ T5.finiteVolumeMeasure thermodynamic cutoff
          (T5.diagonalVolume thermodynamic cutoff)
  ; moments = moments inputs
  ; UniformlyIntegrable = UniformlyIntegrable inputs
  ; witnessImpliesUniformlyIntegrable = witnessImpliesUniformlyIntegrable inputs
  ; boundedObservableTail = boundedObservableTail inputs
  ; boundedObservableHasWitness = boundedObservableHasWitness inputs
  ; weakConvergencePlusUniformIntegrability =
      weakConvergencePlusUniformIntegrability inputs
  }

preferredDiagonalMeasureSameObject :
  ∀ {Measure Observable Scalar}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData Measure Observable Scalar}
    (inputs :
      PreferredDiagonalExpectationProducerInputs
        Measure Observable Scalar thermodynamic)
    cutoff →
  T5.diagonalMeasure
    (compilePreferredDiagonalExpectationProducer inputs) cutoff
  ≡ T5.finiteVolumeMeasure thermodynamic cutoff
      (T5.diagonalVolume thermodynamic cutoff)
preferredDiagonalMeasureSameObject inputs cutoff = refl

preferredDiagonalExpectationSameObject :
  ∀ {Measure Observable Scalar}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData Measure Observable Scalar}
    (inputs :
      PreferredDiagonalExpectationProducerInputs
        Measure Observable Scalar thermodynamic)
    cutoff observable →
  Gram.expectation (T5.operations thermodynamic)
    (T5.diagonalMeasure
      (compilePreferredDiagonalExpectationProducer inputs) cutoff)
    observable
  ≡ Gram.expectation (T5.operations thermodynamic)
      (T5.finiteVolumeMeasure thermodynamic cutoff
        (T5.diagonalVolume thermodynamic cutoff))
      observable
preferredDiagonalExpectationSameObject inputs cutoff observable = refl

preferredDiagonalExpectationProducerCompilerLevel : ProofLevel
preferredDiagonalExpectationProducerCompilerLevel = machineChecked

preferredDiagonalFiniteVolumeSameObjectLevel : ProofLevel
preferredDiagonalFiniteVolumeSameObjectLevel = machineChecked
