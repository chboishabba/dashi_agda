module DASHI.Planning.PlanningAdmissibleTransitionBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Core.AdmissibleTransitionHyperfabricExact as Transition
import DASHI.Planning.NestedSituatedPlanningExact as Planning

------------------------------------------------------------------------
-- SITUATED PLANNING -> ADMISSIBLE TRANSITION HYPERFABRIC
--
-- A planning action is admitted only when the current and resulting situated
-- states are feasible.  This reuses the generic proof-relevant transition gate
-- and keeps subsystem feasibility distinct from containing-system feasibility.
------------------------------------------------------------------------

PlanningEnabled :
  (system : Planning.SituatedPlanningSystem) →
  Planning.Action system → Planning.State system → Set
PlanningEnabled system action state =
  Planning.Feasible system state
  × Planning.Feasible system (Planning.acts system state action)

planningAsAdmissibleTransitionSystem :
  (system : Planning.SituatedPlanningSystem) →
  Transition.AdmissibleTransitionSystem
planningAsAdmissibleTransitionSystem system =
  Transition.admissibleTransitionSystem
    (Planning.State system)
    ⊤
    (Planning.Action system)
    (λ action _ state → PlanningEnabled system action state)
    (λ action _ state → Planning.acts system state action)
    (Planning.Feasible system)
    (λ action _ state enabled feasible → proj₂ enabled)
    "situated planning feasibility gate"

planningAdmittedStepPreservesFeasibility :
  ∀ {system action state} →
  Transition.AdmittedStep
    (planningAsAdmissibleTransitionSystem system)
    action tt state →
  Planning.Feasible system (Planning.acts system state action)
planningAdmittedStepPreservesFeasibility =
  Transition.admittedStepPreservesInvariant

outerReserveActionIsNotAdmittedFromSpareCapacity :
  Transition.AdmittedStep
    (planningAsAdmissibleTransitionSystem Planning.outerSystem)
    Planning.reserveCapacity tt Planning.gridSpareCapacity → ⊥
outerReserveActionIsNotAdmittedFromSpareCapacity admitted =
  Planning.outerFutureCanBeLost
    (planningAdmittedStepPreservesFeasibility admitted)

record PlanningAdmissibleTransitionBoundary : Set where
  constructor planningAdmissibleTransitionBoundary
  field
    feasibleSubsystemActionAutomaticallyPreservesOuterFeasibility : Bool
    feasibleSubsystemActionAutomaticallyPreservesOuterFeasibilityIsFalse :
      feasibleSubsystemActionAutomaticallyPreservesOuterFeasibility ≡ false

    planningAdmissionCanRequireResultingFeasibility : Bool
    planningAdmissionCanRequireResultingFeasibilityIsTrue :
      planningAdmissionCanRequireResultingFeasibility ≡ true

canonicalPlanningAdmissibleTransitionBoundary :
  PlanningAdmissibleTransitionBoundary
canonicalPlanningAdmissibleTransitionBoundary =
  planningAdmissibleTransitionBoundary false refl true refl
