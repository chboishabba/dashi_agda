module DASHI.Planning.NestedSituatedPlanningExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- NESTED / RECURSIVE SITUATED PLANNING
--
-- The realised output of an outer system may provide the carrier/environment
-- for an inner system.  Inner optimisation therefore does not imply outer
-- admissibility: cross-scale resource use may shrink the outer future cone.
------------------------------------------------------------------------

record SituatedPlanningSystem : Set₁ where
  field
    State    : Set
    Resource : Set
    Action   : Set

    Feasible : State → Set
    Uses     : State → Resource → Set
    acts     : State → Action → State

open SituatedPlanningSystem public

record NestedSystems
    (outer inner : SituatedPlanningSystem) : Set₁ where
  field
    Contains : Set
    realisedOuterProvidesInnerCarrier : Set

open NestedSystems public

record CrossScaleResourceCoupling
    (outer inner : SituatedPlanningSystem) : Set₁ where
  field
    SharedResource : Set
    outerResource  : SharedResource → Resource outer
    innerResource  : SharedResource → Resource inner

open CrossScaleResourceCoupling public

------------------------------------------------------------------------
-- No automatic promotion from inner optimality to outer admissibility.
------------------------------------------------------------------------

data InnerOptimalityImpliesOuterAdmissibilityPermission : Set where

innerOptimalityDoesNotAutoPromoteToOuterAdmissibility :
  InnerOptimalityImpliesOuterAdmissibilityPermission → ⊥
innerOptimalityDoesNotAutoPromoteToOuterAdmissibility ()

------------------------------------------------------------------------
-- Concrete finite witness: a subsystem can be feasible before and after its
-- own action while the containing system loses a feasible state.
------------------------------------------------------------------------

data OuterState : Set where
  gridSpareCapacity gridCommitted : OuterState

data InnerState : Set where
  computeUnbuilt computeBuilt : InnerState

data ResourceCode : Set where
  electricity : ResourceCode

data OuterAction : Set where
  reserveCapacity : OuterAction

data InnerAction : Set where
  buildCompute : InnerAction

OuterFeasible : OuterState → Set
OuterFeasible gridSpareCapacity = ⊤
OuterFeasible gridCommitted = ⊥

InnerFeasible : InnerState → Set
InnerFeasible computeUnbuilt = ⊤
InnerFeasible computeBuilt = ⊤

outerSystem : SituatedPlanningSystem
outerSystem =
  record
    { State = OuterState
    ; Resource = ResourceCode
    ; Action = OuterAction
    ; Feasible = OuterFeasible
    ; Uses = λ _ _ → ⊤
    ; acts = λ _ _ → gridCommitted
    }

innerSystem : SituatedPlanningSystem
innerSystem =
  record
    { State = InnerState
    ; Resource = ResourceCode
    ; Action = InnerAction
    ; Feasible = InnerFeasible
    ; Uses = λ _ _ → ⊤
    ; acts = λ _ _ → computeBuilt
    }

innerActionRemainsInnerFeasible : Feasible innerSystem computeBuilt
innerActionRemainsInnerFeasible = tt

outerFutureCanBeLost : Feasible outerSystem gridCommitted → ⊥
outerFutureCanBeLost feasible = feasible

subsystemCanRemainFeasibleWhileContainingSystemLosesFeasibility :
  Feasible innerSystem computeBuilt ×
  (Feasible outerSystem gridCommitted → ⊥)
subsystemCanRemainFeasibleWhileContainingSystemLosesFeasibility =
  innerActionRemainsInnerFeasible , outerFutureCanBeLost
