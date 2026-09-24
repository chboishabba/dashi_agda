{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5MarkedPreferredExpectationRound445Exact where

------------------------------------------------------------------------
-- ROUND445 / MARKED-FP MOMENTS -> PREFERRED DIAGONAL EXPECTATION PRODUCER
--
-- The preferred diagonal producer should not accept an unrelated moment object
-- once the literal marked-polymer moment closure has been realized on the same
-- thermodynamic family.  R444 constructs exactly the ExponentialMomentProducer
-- it needs.
--
-- R445 therefore removes "choose moments again" from the preferred producer.
-- The remaining inputs are the orthogonal continuum-tail / bounded-observable
-- semantics, not a second moment theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PreferredDiagonalExpectationProducerExact as Preferred
import DASHI.Physics.YangMills.BalabanClayT5PhysicalClusterMomentCompactnessExact as Physical
import DASHI.Physics.YangMills.BalabanClayT5MarkedFernandezProcacciExact as FP
import DASHI.Physics.YangMills.BalabanClayT5MarkedMomentProducerRound444Exact as R444

record MarkedPreferredExpectationInputs
    {Measure Observable Polymer : Set}
    (thermodynamic :
      T5.PhysicalThermodynamicClusterData Measure Observable ℚ)
    (model : FP.AbstractPolymerModel Polymer)
    (marked : FP.MarkedActivityData Polymer Observable model)
    (closure : Physical.MarkedMomentClosure Polymer Observable model marked)
    : Set₁ where
  field
    momentRealization :
      R444.MarkedMomentTypedRealization
        thermodynamic
        (Preferred.selectedFiniteVolumeSequence thermodynamic)
        model marked closure

    boundedObservableTail : ∀ observable →
      T5.BoundedObservable thermodynamic observable →
      T5.TailControlledConvergence ℚ
        (Gram.Converges (T5.scalarConvergence thermodynamic))
        (λ cutoff →
          Gram.expectation (T5.operations thermodynamic)
            (Preferred.selectedFiniteVolumeSequence thermodynamic cutoff)
            observable)
        (Gram.expectation (T5.operations thermodynamic)
          (T5.continuumMeasure thermodynamic) observable)

    boundedObservableHasWitness : ∀ observable →
      T5.BoundedObservable thermodynamic observable → Set

    weakConvergencePlusUniformIntegrability :
      ∀ sequence →
      T5.UniformIntegrabilityWitness Observable ℚ sequence → Set

open MarkedPreferredExpectationInputs public

asPreferredDiagonalExpectationInputs :
  ∀ {Measure Observable Polymer}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData Measure Observable ℚ}
    {model : FP.AbstractPolymerModel Polymer}
    {marked : FP.MarkedActivityData Polymer Observable model}
    {closure : Physical.MarkedMomentClosure Polymer Observable model marked} →
  MarkedPreferredExpectationInputs thermodynamic model marked closure →
  Preferred.PreferredDiagonalExpectationProducerInputs
    Measure Observable ℚ thermodynamic
asPreferredDiagonalExpectationInputs inputs = record
  { Preferred.PreferredDiagonalExpectationProducerInputs.moments =
      R444.compileExponentialMomentProducer
        (momentRealization inputs)
  ; Preferred.PreferredDiagonalExpectationProducerInputs.UniformlyIntegrable =
      λ sequence → T5.UniformIntegrabilityWitness _ _ sequence
  ; Preferred.PreferredDiagonalExpectationProducerInputs.witnessImpliesUniformlyIntegrable =
      λ witness → witness
  ; Preferred.PreferredDiagonalExpectationProducerInputs.boundedObservableTail =
      boundedObservableTail inputs
  ; Preferred.PreferredDiagonalExpectationProducerInputs.boundedObservableHasWitness =
      boundedObservableHasWitness inputs
  ; Preferred.PreferredDiagonalExpectationProducerInputs.weakConvergencePlusUniformIntegrability =
      weakConvergencePlusUniformIntegrability inputs
  }

compileMarkedPreferredExpectationProducer :
  ∀ {Measure Observable Polymer}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData Measure Observable ℚ}
    {model : FP.AbstractPolymerModel Polymer}
    {marked : FP.MarkedActivityData Polymer Observable model}
    {closure : Physical.MarkedMomentClosure Polymer Observable model marked} →
  MarkedPreferredExpectationInputs thermodynamic model marked closure →
  T5.PhysicalExpectationProducerData Measure Observable ℚ
compileMarkedPreferredExpectationProducer inputs =
  Preferred.compilePreferredDiagonalExpectationProducer
    (asPreferredDiagonalExpectationInputs inputs)

selectedMomentsAreMarkedMoments :
  ∀ {Measure Observable Polymer}
    {thermodynamic :
      T5.PhysicalThermodynamicClusterData Measure Observable ℚ}
    {model : FP.AbstractPolymerModel Polymer}
    {marked : FP.MarkedActivityData Polymer Observable model}
    {closure : Physical.MarkedMomentClosure Polymer Observable model marked}
    (inputs :
      MarkedPreferredExpectationInputs thermodynamic model marked closure) →
  T5.moments (compileMarkedPreferredExpectationProducer inputs)
  ≡
  R444.compileExponentialMomentProducer (momentRealization inputs)
selectedMomentsAreMarkedMoments inputs = refl

round445MarkedPreferredExpectationCompilerLevel : ProofLevel
round445MarkedPreferredExpectationCompilerLevel = machineChecked

round445MarkedMomentSameObjectLevel : ProofLevel
round445MarkedMomentSameObjectLevel = machineChecked

round445BoundedTailInputsLevel : ProofLevel
round445BoundedTailInputsLevel = conditional

round445IndependentMomentProducerRequired : Bool
round445IndependentMomentProducerRequired = false
