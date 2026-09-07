{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5CoerciveMomentMarkovContainmentExact where

------------------------------------------------------------------------
-- COERCIVE MOMENT + MARKOV AUTHORITY -> COMPACT CONTAINMENT
--
-- The selected diagonal expectation producer already owns a literal cutoff-
-- indexed moment inequality. Historical T5 compactness ledgers then jump to
-- tightness through Set-valued receipts. This module isolates the exact typed
-- physical geometry needed by the generic Markov/sublevel argument.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5MomentCompactContainmentExact as Moment

------------------------------------------------------------------------
-- Generic probability-theory authority.
--
-- It does not certify Yang--Mills coercivity or compactness. Those arrive as
-- explicit premises on the exact selected physical observable/topology.
------------------------------------------------------------------------

record MarkovCompactContainmentAuthority
    (Measure Observable Scalar Epsilon Witness : Set) : Set₁ where
  field
    Admissible : Epsilon → Witness → Set
    Controls : Epsilon → Witness → Measure → Set

    NonnegativeObservable : Observable → Set
    CoerciveForSelectedTopology : Observable → Set
    sublevelWitness : Observable → Nat → Epsilon → Witness

    markovMomentBoundControlsSublevelComplement :
      ∀ {operations measureSequence RenormalizedObservable}
        (producer :
          T5.ExponentialMomentProducer operations measureSequence
            RenormalizedObservable)
        observable degree epsilon cutoff →
      NonnegativeObservable observable →
      CoerciveForSelectedTopology observable →
      Admissible epsilon (sublevelWitness observable degree epsilon) →
      Moment.MomentBoundAt producer degree observable cutoff →
      Controls epsilon
        (sublevelWitness observable degree epsilon)
        (measureSequence cutoff)

open MarkovCompactContainmentAuthority public

------------------------------------------------------------------------
-- Exact physical same-object/coercivity bridge.
------------------------------------------------------------------------

record PhysicalCoerciveMomentObservableBridge
    (Measure Observable Scalar Epsilon Witness : Set)
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar)
    (authority :
      MarkovCompactContainmentAuthority
        Measure Observable Scalar Epsilon Witness) : Set₁ where
  field
    measureLimit : Limit.SequentialLimit Measure

    coerciveObservable : Epsilon → Observable
    coerciveMomentOrder : Epsilon → Nat

    coerciveObservableRenormalized : ∀ epsilon →
      T5.RenormalizedObservable
        (T5.thermodynamic expectationData)
        (coerciveObservable epsilon)

    coerciveObservableNonnegative : ∀ epsilon →
      NonnegativeObservable authority (coerciveObservable epsilon)

    -- This is the exact same-object theorem missing from the historical reuse
    -- surface: the observable integrated against diagonalMeasure is the physical
    -- gauge-field coercive observable, not merely a similarly named finite form.
    gaugeFieldCoerciveObservableSameObject : ∀ epsilon →
      CoerciveForSelectedTopology authority (coerciveObservable epsilon)

    -- The chosen sublevel witness is compact/admissible in the selected measure
    -- topology. This is the physical topology half of compact containment.
    coerciveSublevelCompactInSelectedTopology : ∀ epsilon →
      Admissible authority epsilon
        (sublevelWitness authority
          (coerciveObservable epsilon)
          (coerciveMomentOrder epsilon)
          epsilon)

open PhysicalCoerciveMomentObservableBridge public

compileMomentCompactContainmentInputs :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    {authority :
      MarkovCompactContainmentAuthority
        Measure Observable Scalar Epsilon Witness} →
  PhysicalCoerciveMomentObservableBridge
    Measure Observable Scalar Epsilon Witness expectationData authority →
  Moment.MomentCompactContainmentInputs
    Measure Observable Scalar Epsilon Witness expectationData
compileMomentCompactContainmentInputs {authority = authority} bridge = record
  { measureLimit = measureLimit bridge
  ; Admissible = Admissible authority
  ; Controls = Controls authority
  ; tightnessObservable = coerciveObservable bridge
  ; momentOrder = coerciveMomentOrder bridge
  ; compactWitness = λ epsilon →
      sublevelWitness authority
        (coerciveObservable bridge epsilon)
        (coerciveMomentOrder bridge epsilon)
        epsilon
  ; tightnessObservableRenormalized = coerciveObservableRenormalized bridge
  ; compactWitnessAdmissible =
      coerciveSublevelCompactInSelectedTopology bridge
  ; momentBoundControlsCompactComplement = λ epsilon cutoff bound →
      markovMomentBoundControlsSublevelComplement authority
        (T5.moments _)
        (coerciveObservable bridge epsilon)
        (coerciveMomentOrder bridge epsilon)
        epsilon cutoff
        (coerciveObservableNonnegative bridge epsilon)
        (gaugeFieldCoerciveObservableSameObject bridge epsilon)
        (coerciveSublevelCompactInSelectedTopology bridge epsilon)
        bound
  }

coerciveMomentMarkovContainmentCompilerLevel : ProofLevel
coerciveMomentMarkovContainmentCompilerLevel = machineChecked

markovCompactContainmentAuthorityLevel : ProofLevel
markovCompactContainmentAuthorityLevel = standardImported

physicalCoerciveMomentObservableSameObjectLevel : ProofLevel
physicalCoerciveMomentObservableSameObjectLevel = conditional

physicalCoerciveSublevelCompactnessLevel : ProofLevel
physicalCoerciveSublevelCompactnessLevel = conditional
