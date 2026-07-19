module DASHI.Biology.Core.ContextIndexedSystem where

open import Agda.Builtin.Equality using (_≡_)

-- Shared substrate-neutral interfaces for the biology recovery tower.
-- Context is explicit because biological observables and functions are not
-- generally determined by a microscopic carrier in isolation.

record ContextIndexedProjection : Set₁ where
  field
    Hidden      : Set
    Context     : Set
    Observable  : Set
    project     : Context → Hidden → Observable

record OpenControlledSystem : Set₁ where
  field
    State       : Set
    Context     : Set
    Action      : Set
    Disturbance : Set

    step        : Context → Action → State → State
    disturb     : Disturbance → State → State

    Admissible  : Context → State → Set
    Goal        : Context → State → Set

record GoalCorrectionWitness
  (S : OpenControlledSystem) : Set₁ where
  open OpenControlledSystem S
  field
    policy : Context → State → Disturbance → Action

    recovers :
      (c : Context) (x : State) → Goal c x →
      (d : Disturbance) →
      Goal c (step c (policy c (disturb d x) d) (disturb d x))

record QuotientGoal : Set₁ where
  field
    MicroState  : Set
    MacroState  : Set
    GoalClass   : Set

    coarseGrain : MicroState → MacroState
    classify    : MacroState → GoalClass
    target      : GoalClass

    SameGoal : MicroState → MicroState → Set
    sameGoalSound :
      (x y : MicroState) → SameGoal x y →
      classify (coarseGrain x) ≡ classify (coarseGrain y)

record OpenSystemBudget : Set₁ where
  field
    State       : Set
    Resource    : Set
    EntropyFlow : Set
    Environment : Set

    resourceAt  : State → Resource
    entropyFlow : Environment → State → EntropyFlow

    LocallyMaintained : Environment → State → Set
    ExportsEntropy     : Environment → State → Set
