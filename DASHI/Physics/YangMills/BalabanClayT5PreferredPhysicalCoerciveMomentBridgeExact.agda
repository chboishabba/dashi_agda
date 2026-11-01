{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5PreferredPhysicalCoerciveMomentBridgeExact where

------------------------------------------------------------------------
-- PREFERRED PHYSICAL COERCIVE-MOMENT BRIDGE
--
-- The marked/exponential-moment machinery is quantified over every admissible
-- Observable.  Therefore the preferred route should not first choose an
-- arbitrary moment observable and later prove it equals the physical coercive
-- observable.  Choose the physical coercive observable itself as the moment
-- observable.  The same-object theorem is then definitional (`refl`).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5CoerciveMomentMarkovContainmentExact as Coercive

record PreferredPhysicalCoerciveMomentInputs
    (Measure Observable Scalar Epsilon Witness : Set)
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar)
    (authority :
      Coercive.MarkovCompactContainmentAuthority
        Measure Observable Scalar Epsilon Witness) : Set₁ where
  field
    measureLimit : Limit.SequentialLimit Measure

    -- This one value is used both as the physical coercive observable and as
    -- the literal observable passed to the selected diagonal moment theorem.
    physicalCoerciveObservable : Epsilon → Observable
    coerciveMomentOrder : Epsilon → Nat

    physicalCoerciveObservableRenormalized : ∀ epsilon →
      T5.RenormalizedObservable
        (T5.thermodynamic expectationData)
        (physicalCoerciveObservable epsilon)

    physicalCoerciveObservableNonnegative : ∀ epsilon →
      Coercive.NonnegativeObservable authority
        (physicalCoerciveObservable epsilon)

    physicalCoerciveObservableCoercive : ∀ epsilon →
      Coercive.CoerciveForSelectedTopology authority
        (physicalCoerciveObservable epsilon)

    physicalCoerciveSublevelCompactInSelectedTopology : ∀ epsilon →
      Coercive.Admissible authority epsilon
        (Coercive.sublevelWitness authority
          (physicalCoerciveObservable epsilon)
          (coerciveMomentOrder epsilon)
          epsilon)

open PreferredPhysicalCoerciveMomentInputs public

compilePreferredPhysicalCoerciveMomentBridge :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    {authority :
      Coercive.MarkovCompactContainmentAuthority
        Measure Observable Scalar Epsilon Witness} →
  PreferredPhysicalCoerciveMomentInputs
    Measure Observable Scalar Epsilon Witness expectationData authority →
  Coercive.PhysicalCoerciveMomentObservableBridge
    Measure Observable Scalar Epsilon Witness expectationData authority
compilePreferredPhysicalCoerciveMomentBridge inputs = record
  { measureLimit = measureLimit inputs
  ; momentObservable = physicalCoerciveObservable inputs
  ; physicalCoerciveObservable = physicalCoerciveObservable inputs
  ; coerciveMomentOrder = coerciveMomentOrder inputs
  ; momentObservableRenormalized =
      physicalCoerciveObservableRenormalized inputs
  ; momentObservableNonnegative =
      physicalCoerciveObservableNonnegative inputs
  ; physicalCoerciveObservableCoercive =
      physicalCoerciveObservableCoercive inputs
  ; momentObservableIsPhysicalCoerciveObservable = λ epsilon → refl
  ; coerciveSublevelCompactInSelectedTopology =
      physicalCoerciveSublevelCompactInSelectedTopology inputs
  }

preferredMomentObservableSameObject :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    {authority :
      Coercive.MarkovCompactContainmentAuthority
        Measure Observable Scalar Epsilon Witness}
    (inputs :
      PreferredPhysicalCoerciveMomentInputs
        Measure Observable Scalar Epsilon Witness expectationData authority)
    epsilon →
  Coercive.momentObservable
    (compilePreferredPhysicalCoerciveMomentBridge inputs) epsilon
  ≡ Coercive.physicalCoerciveObservable
      (compilePreferredPhysicalCoerciveMomentBridge inputs) epsilon
preferredMomentObservableSameObject inputs epsilon = refl

preferredPhysicalCoerciveMomentBridgeCompilerLevel : ProofLevel
preferredPhysicalCoerciveMomentBridgeCompilerLevel = machineChecked

preferredMomentObservableSameObjectLevel : ProofLevel
preferredMomentObservableSameObjectLevel = machineChecked

physicalCoerciveObservableRenormalizationLevel : ProofLevel
physicalCoerciveObservableRenormalizationLevel = conditional

physicalCoerciveObservableNonnegativityLevel : ProofLevel
physicalCoerciveObservableNonnegativityLevel = conditional

physicalCoerciveObservableCoercivityLevel : ProofLevel
physicalCoerciveObservableCoercivityLevel = conditional

physicalCoerciveSublevelCompactnessLevel : ProofLevel
physicalCoerciveSublevelCompactnessLevel = conditional
