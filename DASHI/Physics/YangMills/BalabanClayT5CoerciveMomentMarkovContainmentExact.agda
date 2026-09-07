{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5CoerciveMomentMarkovContainmentExact where

------------------------------------------------------------------------
-- COERCIVE MOMENT + MARKOV AUTHORITY -> COMPACT CONTAINMENT
--
-- The selected diagonal expectation producer already owns a literal cutoff-
-- indexed moment inequality.  The historical compactness ledgers did not type
-- the remaining geometric step.  This module isolates that step into the exact
-- same-object/coercivity and compact-sublevel hypotheses consumed by Markov.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5MomentCompactContainmentExact as Moment

------------------------------------------------------------------------
-- Standard Markov/sublevel authority.  This is generic probability theory,
-- not Yang--Mills-specific analysis.
------------------------------------------------------------------------

record MarkovCompactContainmentAuthority
    (Measure Observable Scalar Epsilon Witness : Set) : Set₁ where
  field
    Admissible : Epsilon → Witness → Set
    Controls : Epsilon → Witness → Measure → Set

    -- A nonnegative/coercive observable and a compact sublevel witness are
    -- enough to turn a moment upper bound into tail control.
    NonnegativeObservable : Observable → Set
    CompactSublevelWitness : Observable → Nat → Epsilon → Witness

    compactSublevelAdmissible :
      ∀ observable degree epsilon →
      Admissible epsilon (CompactSublevelWitness observable degree epsilon)

    markovMomentBoundControlsSublevelComplement :
      ∀ {operations measureSequence RenormalizedObservable}
        (producer :
          T5.ExponentialMomentProducer operations measureSequence
            RenormalizedObservable)
        observable degree epsilon cutoff →
      NonnegativeObservable observable →
      Moment.MomentBoundAt producer degree observable cutoff →
      Controls epsilon
        (CompactSublevelWitness observable degree epsilon)
        (measureSequence cutoff)

open MarkovCompactContainmentAuthority public

------------------------------------------------------------------------
-- Yang--Mills same-object bridge.
--
-- This is deliberately the only physical seam.  It says that an observable on
-- the exact expectation-producer carrier is the coercive gauge-field observable
-- whose sublevel sets are compact in the selected measure topology.
------------------------------------------------------------------------

record PhysicalCoerciveMomentObservableBridge
    (Measure Observable Scalar Epsilon Witness : Set)
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar)
    (authority :
      MarkovCompactContainmentAuthority
        Measure Observable Scalar Epsilon Witness) : Set₁ where
  field
    measureLimit :
      DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact.SequentialLimit Measure

    coerciveObservable : Epsilon → Observable
    coerciveMomentOrder : Epsilon → Nat

    coerciveObservableRenormalized : ∀ epsilon →
      T5.RenormalizedObservable
        (T5.thermodynamic expectationData)
        (coerciveObservable epsilon)

    coerciveObservableNonnegative : ∀ epsilon →
      NonnegativeObservable authority (coerciveObservable epsilon)

    -- Same-object theorem: this is not merely a similarly named finite-carrier
    -- energy.  It is the observable interpreted by the selected diagonal
    -- physical measure producer.
    gaugeFieldCoerciveObservableSameObject : ∀ epsilon → Set

    -- Physical geometry/topology theorem: the authority's chosen sublevel
    -- witness really is compact/admissible in the selected gauge-field topology.
    coerciveSublevelCompactInSelectedTopology : ∀ epsilon → Set

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
compileMomentCompactContainmentInputs bridge = record
  { measureLimit = measureLimit bridge
  ; Admissible = Admissible _
  ; Controls = Controls _
  ; tightnessObservable = coerciveObservable bridge
  ; momentOrder = coerciveMomentOrder bridge
  ; compactWitness = λ epsilon →
      CompactSublevelWitness _
        (coerciveObservable bridge epsilon)
        (coerciveMomentOrder bridge epsilon)
        epsilon
  ; tightnessObservableRenormalized = coerciveObservableRenormalized bridge
  ; compactWitnessAdmissible = λ epsilon →
      compactSublevelAdmissible _
        (coerciveObservable bridge epsilon)
        (coerciveMomentOrder bridge epsilon)
        epsilon
  ; momentBoundControlsCompactComplement = λ epsilon cutoff bound →
      markovMomentBoundControlsSublevelComplement _
        (T5.moments _)
        (coerciveObservable bridge epsilon)
        (coerciveMomentOrder bridge epsilon)
        epsilon cutoff
        (coerciveObservableNonnegative bridge epsilon)
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
