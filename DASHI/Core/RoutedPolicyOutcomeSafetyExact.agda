module DASHI.Core.RoutedPolicyOutcomeSafetyExact where

------------------------------------------------------------------------
-- ROUTING OBSERVATION != OUTCOME OBSERVATION
--
-- PolicyRelativeProjectionSafety uses one projection both to choose an action
-- and to compare post-action observations.  Several repo domains need the
-- more general shape
--
--   routeObservation   : State -> Routing
--   outcomeObservation : State -> Outcome.
--
-- A public rights/entitlement surface, triage label, current query, or sensor
-- code can therefore be retained for one role without being promoted to the
-- complete carrier for another role.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.PolicyRelativeProjectionSafety as Policy
import DASHI.Core.TypedDependencyCore as Dependency

record RoutedInterventionPolicy (Routing Action : Set) : Set where
  constructor routedInterventionPolicy
  field
    chooseAction : Routing → Action
open RoutedInterventionPolicy public

record RoutedPolicyOutcomeSafety
    {State Action Routing Outcome : Set}
    (system : Dependency.DependentActionSystem State Action)
    (routeObservation : State → Routing)
    (outcomeObservation : State → Outcome)
    (policy : RoutedInterventionPolicy Routing Action) : Set₁ where
  constructor routedPolicyOutcomeSafety
  field
    selectedStepOutcomeCongruence :
      ∀ {left right leftAfter rightAfter action} →
      routeObservation left ≡ routeObservation right →
      chooseAction policy (routeObservation left) ≡ action →
      chooseAction policy (routeObservation right) ≡ action →
      Reachability.Executes system (action ∷ []) left leftAfter →
      Reachability.Executes system (action ∷ []) right rightAfter →
      outcomeObservation leftAfter ≡ outcomeObservation rightAfter
open RoutedPolicyOutcomeSafety public

record RoutedPolicyOutcomeDefect
    {State Action Routing Outcome : Set}
    (system : Dependency.DependentActionSystem State Action)
    (routeObservation : State → Routing)
    (outcomeObservation : State → Outcome)
    (policy : RoutedInterventionPolicy Routing Action) : Set₁ where
  constructor routedPolicyOutcomeDefect
  field
    left right leftAfter rightAfter : State
    selectedAction : Action
    sameCurrentRoutingObservation :
      routeObservation left ≡ routeObservation right
    leftPolicySelectsAction :
      chooseAction policy (routeObservation left) ≡ selectedAction
    rightPolicySelectsAction :
      chooseAction policy (routeObservation right) ≡ selectedAction
    leftExecution :
      Reachability.Executes system (selectedAction ∷ []) left leftAfter
    rightExecution :
      Reachability.Executes system (selectedAction ∷ []) right rightAfter
    futureOutcomesDiffer :
      outcomeObservation leftAfter ≡ outcomeObservation rightAfter → ⊥
open RoutedPolicyOutcomeDefect public

routedDefectContradictsSafety :
  ∀ {State Action Routing Outcome}
    {system : Dependency.DependentActionSystem State Action}
    {routeObservation : State → Routing}
    {outcomeObservation : State → Outcome}
    {policy : RoutedInterventionPolicy Routing Action} →
  RoutedPolicyOutcomeSafety
    system routeObservation outcomeObservation policy →
  RoutedPolicyOutcomeDefect
    system routeObservation outcomeObservation policy →
  ⊥
routedDefectContradictsSafety safety defect =
  futureOutcomesDiffer defect
    (selectedStepOutcomeCongruence safety
      (sameCurrentRoutingObservation defect)
      (leftPolicySelectsAction defect)
      (rightPolicySelectsAction defect)
      (leftExecution defect)
      (rightExecution defect))

------------------------------------------------------------------------
-- The existing policy-relative theory is the diagonal special case where the
-- routing and outcome observers are the same.
------------------------------------------------------------------------

fromPolicyRelativeSafety :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {policy : Policy.CoarseInterventionPolicy Observation Action} →
  Policy.PolicyRelativeSafety system project policy →
  RoutedPolicyOutcomeSafety
    system project project
    (routedInterventionPolicy (Policy.chooseAction policy))
fromPolicyRelativeSafety safety =
  routedPolicyOutcomeSafety
    (Policy.selectedStepCongruence safety)

fromPolicyExposedDefect :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {policy : Policy.CoarseInterventionPolicy Observation Action} →
  Policy.PolicyExposedQuotientDefect system project policy →
  RoutedPolicyOutcomeDefect
    system project project
    (routedInterventionPolicy (Policy.chooseAction policy))
fromPolicyExposedDefect defect = record
  { left = Policy.left defect
  ; right = Policy.right defect
  ; leftAfter = Policy.leftAfter defect
  ; rightAfter = Policy.rightAfter defect
  ; selectedAction = Policy.selectedAction defect
  ; sameCurrentRoutingObservation = Policy.sameCurrentObservation defect
  ; leftPolicySelectsAction = Policy.leftPolicySelectsAction defect
  ; rightPolicySelectsAction = Policy.rightPolicySelectsAction defect
  ; leftExecution = Policy.leftExecution defect
  ; rightExecution = Policy.rightExecution defect
  ; futureOutcomesDiffer = Policy.selectedFutureObservationsDiffer defect
  }

record RoutedPolicyOutcomeBoundary : Set where
  constructor routedPolicyOutcomeBoundary
  field
    routingAndOutcomeObserversMayDiffer : Bool
    routingAndOutcomeObserversMayDifferIsTrue :
      routingAndOutcomeObserversMayDiffer ≡ true
    oldPolicySafetyRecoveredOnDiagonal : Bool
    oldPolicySafetyRecoveredOnDiagonalIsTrue :
      oldPolicySafetyRecoveredOnDiagonal ≡ true
    validObservationForOneRoleAutomaticallyValidForAllRoles : Bool
    validObservationForOneRoleAutomaticallyValidForAllRolesIsFalse :
      validObservationForOneRoleAutomaticallyValidForAllRoles ≡ false

canonicalRoutedPolicyOutcomeBoundary : RoutedPolicyOutcomeBoundary
canonicalRoutedPolicyOutcomeBoundary =
  routedPolicyOutcomeBoundary true refl true refl false refl
