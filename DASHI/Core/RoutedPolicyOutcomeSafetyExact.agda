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
-- The policy carrier itself is NOT duplicated here.  We reuse the repository's
-- existing CoarseInterventionPolicy and its factorized-lift/naturality theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Core.PolicyObserverFactorizationNaturalityExact as PolicyNaturality
import DASHI.Core.PolicyRelativeProjectionSafety as Policy
import DASHI.Core.TypedDependencyCore as Dependency

record RoutedPolicyOutcomeSafety
    {State Action Routing Outcome : Set}
    (system : Dependency.DependentActionSystem State Action)
    (routeObservation : State → Routing)
    (outcomeObservation : State → Outcome)
    (policy : Policy.CoarseInterventionPolicy Routing Action) : Set₁ where
  constructor routedPolicyOutcomeSafety
  field
    selectedStepOutcomeCongruence :
      ∀ {left right leftAfter rightAfter action} →
      routeObservation left ≡ routeObservation right →
      Policy.chooseAction policy (routeObservation left) ≡ action →
      Policy.chooseAction policy (routeObservation right) ≡ action →
      Reachability.Executes system (action ∷ []) left leftAfter →
      Reachability.Executes system (action ∷ []) right rightAfter →
      outcomeObservation leftAfter ≡ outcomeObservation rightAfter
open RoutedPolicyOutcomeSafety public

record RoutedPolicyOutcomeDefect
    {State Action Routing Outcome : Set}
    (system : Dependency.DependentActionSystem State Action)
    (routeObservation : State → Routing)
    (outcomeObservation : State → Outcome)
    (policy : Policy.CoarseInterventionPolicy Routing Action) : Set₁ where
  constructor routedPolicyOutcomeDefect
  field
    left right leftAfter rightAfter : State
    selectedAction : Action
    sameCurrentRoutingObservation :
      routeObservation left ≡ routeObservation right
    leftPolicySelectsAction :
      Policy.chooseAction policy (routeObservation left) ≡ selectedAction
    rightPolicySelectsAction :
      Policy.chooseAction policy (routeObservation right) ≡ selectedAction
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
    {policy : Policy.CoarseInterventionPolicy Routing Action} →
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
-- Factorized routing refinement.
--
-- Hold the outcome observer fixed.  PolicyObserverFactorizationNaturalityExact
-- already owns the policy lift and action commuting square.  Using those exact
-- maps, safety for a coarse router is monotone upward to any factorized finer
-- router carrying the same policy decisions.
------------------------------------------------------------------------

routingRefinementPreservesOutcomeSafety :
  ∀ {State Action CoarseRouting FineRouting Outcome : Set}
    {system : Dependency.DependentActionSystem State Action}
    {coarseRoute : State → CoarseRouting}
    {fineRoute : State → FineRouting}
    {outcomeObservation : State → Outcome}
    (refinement : Factorized.FactorizedRefinement coarseRoute fineRoute)
    (coarsePolicy : Policy.CoarseInterventionPolicy CoarseRouting Action) →
  RoutedPolicyOutcomeSafety
    system coarseRoute outcomeObservation coarsePolicy →
  RoutedPolicyOutcomeSafety
    system fineRoute outcomeObservation
    (PolicyNaturality.liftPolicyAlongFactorizedRefinement
      refinement coarsePolicy)
routingRefinementPreservesOutcomeSafety
  refinement coarsePolicy coarseSafety =
  routedPolicyOutcomeSafety proof
  where
    finePolicy : Policy.CoarseInterventionPolicy FineRouting Action
    finePolicy =
      PolicyNaturality.liftPolicyAlongFactorizedRefinement
        refinement coarsePolicy

    proof :
      ∀ {left right leftAfter rightAfter action} →
      fineRoute left ≡ fineRoute right →
      Policy.chooseAction finePolicy (fineRoute left) ≡ action →
      Policy.chooseAction finePolicy (fineRoute right) ≡ action →
      Reachability.Executes system (action ∷ []) left leftAfter →
      Reachability.Executes system (action ∷ []) right rightAfter →
      outcomeObservation leftAfter ≡ outcomeObservation rightAfter
    proof sameFine leftSelects rightSelects leftRun rightRun =
      selectedStepOutcomeCongruence coarseSafety
        (Factorized.factorizedRefinementImpliesRefines refinement
          left right sameFine)
        (trans
          (sym (PolicyNaturality.liftedPolicyNaturality
            refinement coarsePolicy left))
          leftSelects)
        (trans
          (sym (PolicyNaturality.liftedPolicyNaturality
            refinement coarsePolicy right))
          rightSelects)
        leftRun
        rightRun

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
  RoutedPolicyOutcomeSafety system project project policy
fromPolicyRelativeSafety safety =
  routedPolicyOutcomeSafety
    (Policy.selectedStepCongruence safety)

fromPolicyExposedDefect :
  ∀ {State Action Observation}
    {system : Dependency.DependentActionSystem State Action}
    {project : State → Observation}
    {policy : Policy.CoarseInterventionPolicy Observation Action} →
  Policy.PolicyExposedQuotientDefect system project policy →
  RoutedPolicyOutcomeDefect system project project policy
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
    canonicalPolicyCarrierReused : Bool
    canonicalPolicyCarrierReusedIsTrue : canonicalPolicyCarrierReused ≡ true
    oldPolicySafetyRecoveredOnDiagonal : Bool
    oldPolicySafetyRecoveredOnDiagonalIsTrue :
      oldPolicySafetyRecoveredOnDiagonal ≡ true
    safeRoutingRemainsSafeUnderFactorizedRefinement : Bool
    safeRoutingRemainsSafeUnderFactorizedRefinementIsTrue :
      safeRoutingRemainsSafeUnderFactorizedRefinement ≡ true
    splittingOneBadRoutingCollisionAutomaticallyProvesSafety : Bool
    splittingOneBadRoutingCollisionAutomaticallyProvesSafetyIsFalse :
      splittingOneBadRoutingCollisionAutomaticallyProvesSafety ≡ false
    validObservationForOneRoleAutomaticallyValidForAllRoles : Bool
    validObservationForOneRoleAutomaticallyValidForAllRolesIsFalse :
      validObservationForOneRoleAutomaticallyValidForAllRoles ≡ false

canonicalRoutedPolicyOutcomeBoundary : RoutedPolicyOutcomeBoundary
canonicalRoutedPolicyOutcomeBoundary =
  routedPolicyOutcomeBoundary
    true refl true refl true refl true refl false refl false refl
