module DASHI.Core.TargetIndexedActionNonfactorabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- TARGET-INDEXED ACTION NONFACTORABILITY
--
-- A coarse observation need not determine action when the operative target,
-- consumer, or policy context differs.  This is deliberately substrate-neutral:
-- biological control, autonomous software, robotics, planning and governance
-- can instantiate the same theorem shape.
------------------------------------------------------------------------

record TargetIndexedPolicy : Set₁ where
  constructor targetIndexedPolicy
  field
    State Observation Target Action : Set
    observe : State → Observation
    choose : Target → Observation → Action

open TargetIndexedPolicy public

record SameObservationDifferentTargetAction
    (P : TargetIndexedPolicy) : Set where
  constructor sameObservationDifferentTargetAction
  field
    leftState rightState : State P
    leftTarget rightTarget : Target P
    sameObservation : observe P leftState ≡ observe P rightState
    differentAction :
      choose P leftTarget (observe P leftState)
      ≡ choose P rightTarget (observe P rightState) → ⊥

open SameObservationDifferentTargetAction public

------------------------------------------------------------------------
-- Exact finite calibration.
------------------------------------------------------------------------

data ToyState : Set where s₀ s₁ : ToyState
data ToyObservation : Set where sameSignal : ToyObservation
data ToyTarget : Set where repairGoal exploreGoal : ToyTarget
data ToyAction : Set where repairAction exploreAction : ToyAction

toyObserve : ToyState → ToyObservation
toyObserve s₀ = sameSignal
toyObserve s₁ = sameSignal

toyChoose : ToyTarget → ToyObservation → ToyAction
toyChoose repairGoal sameSignal = repairAction
toyChoose exploreGoal sameSignal = exploreAction

toyPolicy : TargetIndexedPolicy
toyPolicy = targetIndexedPolicy ToyState ToyObservation ToyTarget ToyAction toyObserve toyChoose

repairExploreDistinct : repairAction ≡ exploreAction → ⊥
repairExploreDistinct ()

sameSignalDifferentGoalAction : SameObservationDifferentTargetAction toyPolicy
sameSignalDifferentGoalAction =
  sameObservationDifferentTargetAction
    s₀ s₁ repairGoal exploreGoal refl repairExploreDistinct

record TargetIndexedActionBoundary : Set where
  constructor targetIndexedActionBoundary
  field
    sameObservationForcesSameAction : Bool
    sameObservationForcesSameActionIsFalse : sameObservationForcesSameAction ≡ false
    targetMayChangeActionWithoutChangingObservation : Bool
    targetMayChangeActionWithoutChangingObservationIsTrue :
      targetMayChangeActionWithoutChangingObservation ≡ true
    targetIndexedChoiceCreatesExecutionAuthority : Bool
    targetIndexedChoiceCreatesExecutionAuthorityIsFalse :
      targetIndexedChoiceCreatesExecutionAuthority ≡ false

canonicalTargetIndexedActionBoundary : TargetIndexedActionBoundary
canonicalTargetIndexedActionBoundary =
  targetIndexedActionBoundary false refl true refl false refl
