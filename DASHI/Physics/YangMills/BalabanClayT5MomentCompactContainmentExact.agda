{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5MomentCompactContainmentExact where

------------------------------------------------------------------------
-- TYPED MOMENT BOUND -> UNIFORM COMPACT CONTAINMENT
--
-- The existing ExponentialMomentProducer already owns a literal cutoff-indexed
-- polynomial-moment inequality on its selected measureSequence. Historical T5
-- ledgers then jump to tightness through Set-valued receipts. This module keeps
-- the moment inequality as an actual theorem and isolates only the missing
-- coercive/compact-containment interpretation needed to obtain uniform
-- tightness of the selected physical sequence.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5UniformTightnessSubsequenceInheritanceExact as Uniform

------------------------------------------------------------------------
-- Re-state the exact already-owned moment inequality as a named proposition.
------------------------------------------------------------------------

MomentBoundAt :
  ∀ {Measure Observable Scalar}
    {operations : Gram.PhysicalOSOperations Measure Observable Scalar}
    {measureSequence : Nat → Measure}
    {RenormalizedObservable : Observable → Set} →
  T5.ExponentialMomentProducer operations measureSequence RenormalizedObservable →
  Nat → Observable → Nat → Set
MomentBoundAt {operations = operations} {measureSequence = measureSequence}
  producer degree observable cutoff =
  T5.LessEqual producer
    (Gram.expectation operations (measureSequence cutoff)
      (T5.powerObservable producer degree
        (T5.absoluteObservable producer observable)))
    (T5.multiply producer (T5.factorial producer degree)
      (T5.divide producer (T5.exponentialMomentBound producer observable)
        (T5.lambda producer)))

producerMomentBoundAt :
  ∀ {Measure Observable Scalar}
    {operations : Gram.PhysicalOSOperations Measure Observable Scalar}
    {measureSequence : Nat → Measure}
    {RenormalizedObservable : Observable → Set}
    (producer :
      T5.ExponentialMomentProducer operations measureSequence
        RenormalizedObservable)
    degree observable →
  RenormalizedObservable observable → ∀ cutoff →
  MomentBoundAt producer degree observable cutoff
producerMomentBoundAt = T5.singleScaleInsertionMomentBound

------------------------------------------------------------------------
-- Physical compact-containment bridge.
--
-- For each epsilon choose one moment observable/order and one compact witness.
-- The only new analytic implication is that the already-owned moment inequality
-- forces the selected measure to satisfy the compact-containment control.
------------------------------------------------------------------------

record MomentCompactContainmentInputs
    (Measure Observable Scalar Epsilon Witness : Set)
    (expectationData : T5.PhysicalExpectationProducerData
      Measure Observable Scalar) : Set₁ where
  field
    measureLimit : Limit.SequentialLimit Measure

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

    -- This is the remaining physical geometry/coercivity statement. Markov's
    -- inequality or its selected measure-space analogue can inhabit it once the
    -- observable is shown to dominate escape from the chosen compact set.
    momentBoundControlsCompactComplement : ∀ epsilon cutoff →
      MomentBoundAt (T5.moments expectationData)
        (momentOrder epsilon) (tightnessObservable epsilon) cutoff →
      Controls epsilon (compactWitness epsilon)
        (T5.diagonalMeasure expectationData cutoff)

open MomentCompactContainmentInputs public

selectedDiagonalUniformTightnessCertificate :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData : T5.PhysicalExpectationProducerData
      Measure Observable Scalar}
    (inputs : MomentCompactContainmentInputs
      Measure Observable Scalar Epsilon Witness expectationData) →
  Uniform.UniformTightnessCertificate
    Measure Epsilon Witness
    (Admissible inputs) (Controls inputs)
    (T5.diagonalMeasure expectationData)
selectedDiagonalUniformTightnessCertificate
  {expectationData = expectationData} inputs = record
  { witness = compactWitness inputs
  ; witnessAdmissible = compactWitnessAdmissible inputs
  ; controlsAll = λ epsilon cutoff →
      momentBoundControlsCompactComplement inputs epsilon cutoff
        (producerMomentBoundAt
          (T5.moments expectationData)
          (momentOrder inputs epsilon)
          (tightnessObservable inputs epsilon)
          (tightnessObservableRenormalized inputs epsilon)
          cutoff)
  }

compileSelectedPhysicalUniformTightnessInputs :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData : T5.PhysicalExpectationProducerData
      Measure Observable Scalar}
    (inputs : MomentCompactContainmentInputs
      Measure Observable Scalar Epsilon Witness expectationData) →
  Uniform.SelectedPhysicalUniformTightnessInputs Measure Epsilon Witness
compileSelectedPhysicalUniformTightnessInputs
  {expectationData = expectationData} inputs = record
  { convergence = measureLimit inputs
  ; sequence = T5.diagonalMeasure expectationData
  ; Admissible = Admissible inputs
  ; Controls = Controls inputs
  ; selectedSequenceUniformlyTight =
      selectedDiagonalUniformTightnessCertificate inputs
  }

typedMomentToUniformTightnessCompilerLevel : ProofLevel
typedMomentToUniformTightnessCompilerLevel = machineChecked

-- The moment inequality itself is inherited from the existing expectation
-- producer. The genuinely remaining Yang--Mills input is the compact-containment
-- interpretation of a selected coercive moment observable.
physicalMomentCompactContainmentLevel : ProofLevel
physicalMomentCompactContainmentLevel = conditional
