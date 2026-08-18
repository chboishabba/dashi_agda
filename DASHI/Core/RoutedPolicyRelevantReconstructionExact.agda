module DASHI.Core.RoutedPolicyRelevantReconstructionExact where

------------------------------------------------------------------------
-- POLICY-RELATIVE RECONSTRUCTION
--
-- FutureRelevantBoundaryReconstructionExact shows that a sectioned observer
-- can reconstruct a representative up to a declared future-language relation.
-- Policy routing often needs less: adequacy only for the action selected by a
-- declared policy and a declared outcome observer.
--
-- This module supplies that role-specific relevant equivalence.  It does not
-- identify policy adequacy with exact state reconstruction or world identity.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.BoundaryObservationReconstructionExact as Boundary
import DASHI.Core.FutureObservationLanguageQuotientExact as Future
import DASHI.Core.PolicyRelativeProjectionSafety as Policy
import DASHI.Core.RoutedPolicyOutcomeSafetyExact as Routed
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reachability

record SelectedPolicyOutcomeEquivalent
    {State Action Routing Outcome : Set}
    (system : Dependency.DependentActionSystem State Action)
    (routeObservation : State → Routing)
    (outcomeObservation : State → Outcome)
    (policy : Policy.CoarseInterventionPolicy Routing Action)
    (left right : State) : Set₁ where
  constructor selectedPolicyOutcomeEquivalent
  field
    sameRoutingObservation :
      routeObservation left ≡ routeObservation right
    selectedOutcomeCongruence :
      ∀ {leftAfter rightAfter action} →
      Policy.chooseAction policy (routeObservation left) ≡ action →
      Policy.chooseAction policy (routeObservation right) ≡ action →
      Reachability.Executes system (action ∷ []) left leftAfter →
      Reachability.Executes system (action ∷ []) right rightAfter →
      outcomeObservation leftAfter ≡ outcomeObservation rightAfter

open SelectedPolicyOutcomeEquivalent public

sectionedRoutedPolicySafetyGivesRelevantReconstruction :
  ∀ {State Action Routing Outcome : Set}
    {system : Dependency.DependentActionSystem State Action}
    {routeObservation : State → Routing}
    {outcomeObservation : State → Outcome}
    {policy : Policy.CoarseInterventionPolicy Routing Action} →
  Routed.RoutedPolicyOutcomeSafety
    system routeObservation outcomeObservation policy →
  Future.SectionedProjection routeObservation →
  Boundary.RelevantBoundaryReconstruction
    (SelectedPolicyOutcomeEquivalent
      system routeObservation outcomeObservation policy)
    routeObservation
sectionedRoutedPolicySafetyGivesRelevantReconstruction safety sectioned =
  Boundary.relevantBoundaryReconstruction
    (Future.section sectioned)
    witness
  where
    witness :
      (state : State) →
      SelectedPolicyOutcomeEquivalent
        system routeObservation outcomeObservation policy
        (Future.section sectioned (routeObservation state))
        state
    witness state =
      selectedPolicyOutcomeEquivalent
        (Future.sectionRightInverse sectioned (routeObservation state))
        (λ leftSelects rightSelects leftRun rightRun →
          Routed.selectedStepOutcomeCongruence safety
            (Future.sectionRightInverse sectioned (routeObservation state))
            leftSelects
            rightSelects
            leftRun
            rightRun)

record RoutedPolicyRelevantReconstructionBoundary : Set where
  constructor routedPolicyRelevantReconstructionBoundary
  field
    exactStateRecoveryRequiredForPolicyRouting : Bool
    exactStateRecoveryRequiredForPolicyRoutingIsFalse :
      exactStateRecoveryRequiredForPolicyRouting ≡ false
    sectionedSafeRouterReconstructsPolicyOutcomeEquivalentRepresentative : Bool
    sectionedSafeRouterReconstructsPolicyOutcomeEquivalentRepresentativeIsTrue :
      sectionedSafeRouterReconstructsPolicyOutcomeEquivalentRepresentative ≡ true
    policyOutcomeEquivalenceMeansUniversalFutureEquivalence : Bool
    policyOutcomeEquivalenceMeansUniversalFutureEquivalenceIsFalse :
      policyOutcomeEquivalenceMeansUniversalFutureEquivalence ≡ false
    policyOutcomeEquivalenceMeansWorldIdentity : Bool
    policyOutcomeEquivalenceMeansWorldIdentityIsFalse :
      policyOutcomeEquivalenceMeansWorldIdentity ≡ false

canonicalRoutedPolicyRelevantReconstructionBoundary :
  RoutedPolicyRelevantReconstructionBoundary
canonicalRoutedPolicyRelevantReconstructionBoundary =
  routedPolicyRelevantReconstructionBoundary
    false refl true refl false refl false refl
