{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5SelectedMomentCompactContainmentExact where

------------------------------------------------------------------------
-- SELECTED MOMENT BOUND -> UNIFORM COMPACT CONTAINMENT
--
-- The moment estimate and compact-containment implication do not depend on a
-- measure convergence relation.  This preferred compiler therefore removes the
-- historical `measureLimit` field entirely and produces the existing uniform
-- tightness certificate directly on the selected diagonal sequence.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5MomentCompactContainmentExact as Moment
import DASHI.Physics.YangMills.BalabanClayT5UniformTightnessSubsequenceInheritanceExact as Uniform

record SelectedMomentCompactContainmentInputs
    (Measure Observable Scalar Epsilon Witness : Set)
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar) : Set₁ where
  field
    Admissible : Epsilon → Witness → Set
    Controls : Epsilon → Witness → Measure → Set

    tightnessObservable : Epsilon → Observable
    momentOrder : Epsilon → Nat
    compactWitness : Epsilon → Witness

    tightnessObservableRenormalized : ∀ epsilon →
      T5.RenormalizedObservable
        (T5.thermodynamic expectationData)
        (tightnessObservable epsilon)

    compactWitnessAdmissible : ∀ epsilon →
      Admissible epsilon (compactWitness epsilon)

    momentBoundControlsCompactComplement : ∀ epsilon cutoff →
      Moment.MomentBoundAt (T5.moments expectationData)
        (momentOrder epsilon) (tightnessObservable epsilon) cutoff →
      Controls epsilon (compactWitness epsilon)
        (T5.diagonalMeasure expectationData cutoff)

open SelectedMomentCompactContainmentInputs public

selectedDiagonalUniformTightnessCertificate :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    (inputs : SelectedMomentCompactContainmentInputs
      Measure Observable Scalar Epsilon Witness expectationData) →
  Uniform.UniformTightnessCertificate
    Measure Epsilon Witness
    (Admissible inputs)
    (Controls inputs)
    (T5.diagonalMeasure expectationData)
selectedDiagonalUniformTightnessCertificate
  {expectationData = expectationData} inputs = record
  { witness = compactWitness inputs
  ; witnessAdmissible = compactWitnessAdmissible inputs
  ; controlsAll = λ epsilon cutoff →
      momentBoundControlsCompactComplement inputs epsilon cutoff
        (Moment.producerMomentBoundAt
          (T5.moments expectationData)
          (momentOrder inputs epsilon)
          (tightnessObservable inputs epsilon)
          (tightnessObservableRenormalized inputs epsilon)
          cutoff)
  }

selectedMomentCompactContainmentCompilerLevel : ProofLevel
selectedMomentCompactContainmentCompilerLevel = machineChecked

-- This is now the exact T1 physical theorem: on the literal selected diagonal
-- measure sequence, the already-owned moment bound controls escape from one
-- admissible compact witness.
selectedGlobalMomentCompactContainmentLevel : ProofLevel
selectedGlobalMomentCompactContainmentLevel = conditional
