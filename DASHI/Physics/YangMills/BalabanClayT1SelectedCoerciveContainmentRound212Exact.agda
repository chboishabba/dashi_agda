{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT1SelectedCoerciveContainmentRound212Exact where

------------------------------------------------------------------------
-- ROUND212 / SELECTED COERCIVE OBSERVABLE -> T1 CONTAINMENT
--
-- The current preferred T1 route is entirely on the literal selected diagonal
-- measure sequence.  The older preferred physical-coercive bridge still carried
-- a total SequentialLimit only because it targeted the historical compiler.
--
-- This owner removes that representation inflation.  Choose the physical
-- coercive observable itself as the selected moment observable; if it is
-- nonnegative, coercive for the selected topology, and has admissibly compact
-- sublevels, the existing Markov authority compiles the already-owned selected
-- moment theorem directly to selected compact containment.  No convergence
-- carrier and no post-hoc observable equality theorem are required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5CoerciveMomentMarkovContainmentExact as Coercive
import DASHI.Physics.YangMills.BalabanClayT5SelectedMomentCompactContainmentExact as SelectedMoment
import DASHI.Physics.YangMills.BalabanClayT1PhysicalMeaningRound211Exact as R211

record SelectedPhysicalCoerciveMomentInputs
    (Measure Observable Scalar Epsilon Witness : Set)
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar)
    (authority :
      Coercive.MarkovCompactContainmentAuthority
        Measure Observable Scalar Epsilon Witness) : Set₁ where
  field
    -- One literal observable value serves both as the physical coercive object
    -- and as the observable consumed by the selected moment theorem.
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

open SelectedPhysicalCoerciveMomentInputs public

compileSelectedPhysicalCoerciveContainment :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    {authority :
      Coercive.MarkovCompactContainmentAuthority
        Measure Observable Scalar Epsilon Witness} →
  SelectedPhysicalCoerciveMomentInputs
    Measure Observable Scalar Epsilon Witness expectationData authority →
  SelectedMoment.SelectedMomentCompactContainmentInputs
    Measure Observable Scalar Epsilon Witness expectationData
compileSelectedPhysicalCoerciveContainment {authority = authority} inputs = record
  { Admissible = Coercive.Admissible authority
  ; Controls = Coercive.Controls authority
  ; tightnessObservable = physicalCoerciveObservable inputs
  ; momentOrder = coerciveMomentOrder inputs
  ; compactWitness = λ epsilon →
      Coercive.sublevelWitness authority
        (physicalCoerciveObservable inputs epsilon)
        (coerciveMomentOrder inputs epsilon)
        epsilon
  ; tightnessObservableRenormalized =
      physicalCoerciveObservableRenormalized inputs
  ; compactWitnessAdmissible =
      physicalCoerciveSublevelCompactInSelectedTopology inputs
  ; momentBoundControlsCompactComplement = λ epsilon cutoff bound →
      Coercive.markovMomentBoundControlsSublevelComplement authority
        (T5.moments _)
        (physicalCoerciveObservable inputs epsilon)
        (coerciveMomentOrder inputs epsilon)
        epsilon cutoff
        (physicalCoerciveObservableNonnegative inputs epsilon)
        (physicalCoerciveObservableCoercive inputs epsilon)
        (physicalCoerciveSublevelCompactInSelectedTopology inputs epsilon)
        bound
  }

------------------------------------------------------------------------
-- Physical / introspective implications.
------------------------------------------------------------------------

round212LegacySequentialLimitRequired : Bool
round212LegacySequentialLimitRequired = false

round212PostHocObservableEqualityRequired : Bool
round212PostHocObservableEqualityRequired = false

round212SelectedMarkovContainmentCompilerClosed : Bool
round212SelectedMarkovContainmentCompilerClosed = true

round212RemainingPhysicalInputsAreCoercivityAndCompactSublevels : Bool
round212RemainingPhysicalInputsAreCoercivityAndCompactSublevels = true

round212DirectContainmentRemainsLeastPrivilegeTarget : Bool
round212DirectContainmentRemainsLeastPrivilegeTarget =
  R211.round211DirectContainmentIsLeastPrivilegeTarget

round212ClayPromotion : Bool
round212ClayPromotion = false

round212LegacySequentialLimitRequiredIsFalse :
  round212LegacySequentialLimitRequired ≡ false
round212LegacySequentialLimitRequiredIsFalse = refl

round212PostHocObservableEqualityRequiredIsFalse :
  round212PostHocObservableEqualityRequired ≡ false
round212PostHocObservableEqualityRequiredIsFalse = refl

round212SelectedMarkovContainmentCompilerClosedIsTrue :
  round212SelectedMarkovContainmentCompilerClosed ≡ true
round212SelectedMarkovContainmentCompilerClosedIsTrue = refl

round212ClayPromotionIsFalse : round212ClayPromotion ≡ false
round212ClayPromotionIsFalse = refl

currentYMTerminalCutsetRound212Level : ProofLevel
currentYMTerminalCutsetRound212Level = machineChecked

physicalSelectedCoercivityAndCompactSublevelLevel : ProofLevel
physicalSelectedCoercivityAndCompactSublevelLevel = conditional
