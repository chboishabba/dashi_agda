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

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst)

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
--
-- Two observable values are explicit:
--   * `momentObservable`: the literal Observable consumed by the selected
--     diagonal-measure moment theorem;
--   * `physicalCoerciveObservable`: the observable independently justified by
--     the physical gauge-field coercivity theorem.
--
-- Their identification is an actual equality, not a predicate or Set receipt.
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

    momentObservable : Epsilon → Observable
    physicalCoerciveObservable : Epsilon → Observable
    coerciveMomentOrder : Epsilon → Nat

    momentObservableRenormalized : ∀ epsilon →
      T5.RenormalizedObservable
        (T5.thermodynamic expectationData)
        (momentObservable epsilon)

    momentObservableNonnegative : ∀ epsilon →
      NonnegativeObservable authority (momentObservable epsilon)

    physicalCoerciveObservableCoercive : ∀ epsilon →
      CoerciveForSelectedTopology authority
        (physicalCoerciveObservable epsilon)

    -- Literal same-object theorem. This is the firewall that prevents a
    -- finite-carrier or merely similarly named coercive quantity from paying
    -- the moment observable requirement.
    momentObservableIsPhysicalCoerciveObservable : ∀ epsilon →
      momentObservable epsilon ≡ physicalCoerciveObservable epsilon

    -- The selected moment observable's sublevel witness is compact/admissible
    -- in the selected measure topology.
    coerciveSublevelCompactInSelectedTopology : ∀ epsilon →
      Admissible authority epsilon
        (sublevelWitness authority
          (momentObservable epsilon)
          (coerciveMomentOrder epsilon)
          epsilon)

open PhysicalCoerciveMomentObservableBridge public

momentObservableCoercive :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    {authority :
      MarkovCompactContainmentAuthority
        Measure Observable Scalar Epsilon Witness}
    (bridge :
      PhysicalCoerciveMomentObservableBridge
        Measure Observable Scalar Epsilon Witness expectationData authority)
    epsilon →
  CoerciveForSelectedTopology authority (momentObservable bridge epsilon)
momentObservableCoercive {authority = authority} bridge epsilon =
  subst
    (CoerciveForSelectedTopology authority)
    (Relation.Binary.PropositionalEquality.sym
      (momentObservableIsPhysicalCoerciveObservable bridge epsilon))
    (physicalCoerciveObservableCoercive bridge epsilon)

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
  ; tightnessObservable = momentObservable bridge
  ; momentOrder = coerciveMomentOrder bridge
  ; compactWitness = λ epsilon →
      sublevelWitness authority
        (momentObservable bridge epsilon)
        (coerciveMomentOrder bridge epsilon)
        epsilon
  ; tightnessObservableRenormalized = momentObservableRenormalized bridge
  ; compactWitnessAdmissible =
      coerciveSublevelCompactInSelectedTopology bridge
  ; momentBoundControlsCompactComplement = λ epsilon cutoff bound →
      markovMomentBoundControlsSublevelComplement authority
        (T5.moments _)
        (momentObservable bridge epsilon)
        (coerciveMomentOrder bridge epsilon)
        epsilon cutoff
        (momentObservableNonnegative bridge epsilon)
        (momentObservableCoercive bridge epsilon)
        (coerciveSublevelCompactInSelectedTopology bridge epsilon)
        bound
  }

coerciveMomentMarkovContainmentCompilerLevel : ProofLevel
coerciveMomentMarkovContainmentCompilerLevel = machineChecked

coerciveObservableEqualityTransportLevel : ProofLevel
coerciveObservableEqualityTransportLevel = machineChecked

markovCompactContainmentAuthorityLevel : ProofLevel
markovCompactContainmentAuthorityLevel = standardImported

physicalCoerciveMomentObservableSameObjectLevel : ProofLevel
physicalCoerciveMomentObservableSameObjectLevel = conditional

physicalCoerciveObservableCoercivityLevel : ProofLevel
physicalCoerciveObservableCoercivityLevel = conditional

physicalCoerciveSublevelCompactnessLevel : ProofLevel
physicalCoerciveSublevelCompactnessLevel = conditional
