module DASHI.Core.ObserverAffordanceIncomparabilityExact where

------------------------------------------------------------------------
-- OBSERVER / AFFORDANCE INCOMPARABILITY
--
-- INTERNAL THEOREM-PATTERN PROVENANCE
--
-- Extracted from the independent draft theorem shapes in PR #606
-- (world/perceived/accessible/actionable separation), PR #618
-- (social-ecological affordance cones), PR #620 (normative observer regimes),
-- and PR #603 (observer refinement != actuation/authority).
--
-- This owner is domain-neutral.  It proves only that two state observables can
-- each erase distinctions required by the other.  No political, clinical or
-- ecological interpretation follows from the generic theorem alone.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- Bidirectional non-descent.
------------------------------------------------------------------------

record ObserverAffordanceIncomparability
    {State Observation Affordance : Set}
    (observe : State → Observation)
    (affordance : State → Affordance) : Set where
  constructor observer-affordance-incomparability
  field
    observationCannotRecoverAffordance :
      INF.NonFactorabilityWitness observe affordance
    affordanceCannotRecoverObservation :
      INF.NonFactorabilityWitness affordance observe

open ObserverAffordanceIncomparability public

observationDoesNotDetermineAffordance :
  ∀ {State Observation Affordance : Set}
    {observe : State → Observation}
    {affordance : State → Affordance} →
  ObserverAffordanceIncomparability observe affordance →
  INF.FactorsThrough observe affordance → ⊥
observationDoesNotDetermineAffordance witness =
  INF.witnessRulesOutEveryFlatFactorisation
    (observationCannotRecoverAffordance witness)

affordanceDoesNotDetermineObservation :
  ∀ {State Observation Affordance : Set}
    {observe : State → Observation}
    {affordance : State → Affordance} →
  ObserverAffordanceIncomparability observe affordance →
  INF.FactorsThrough affordance observe → ⊥
affordanceDoesNotDetermineObservation witness =
  INF.witnessRulesOutEveryFlatFactorisation
    (affordanceCannotRecoverObservation witness)

------------------------------------------------------------------------
-- Exact four-state square.
------------------------------------------------------------------------

data SquareState : Set where
  closedApproved
  openApproved
  closedDisapproved
  openDisapproved
  : SquareState

data SquareObservation : Set where
  approved disapproved : SquareObservation

data SquareAffordance : Set where
  closed open : SquareAffordance

squareObservation : SquareState → SquareObservation
squareObservation closedApproved = approved
squareObservation openApproved = approved
squareObservation closedDisapproved = disapproved
squareObservation openDisapproved = disapproved

squareAffordance : SquareState → SquareAffordance
squareAffordance closedApproved = closed
squareAffordance openApproved = open
squareAffordance closedDisapproved = closed
squareAffordance openDisapproved = open

sameApprovalDifferentAffordance :
  INF.NonFactorabilityWitness squareObservation squareAffordance
sameApprovalDifferentAffordance =
  INF.nonFactorabilityWitness
    closedApproved
    openApproved
    refl
    (λ ())

sameAffordanceDifferentApproval :
  INF.NonFactorabilityWitness squareAffordance squareObservation
sameAffordanceDifferentApproval =
  INF.nonFactorabilityWitness
    closedApproved
    closedDisapproved
    refl
    (λ ())

canonicalObserverAffordanceIncomparability :
  ObserverAffordanceIncomparability squareObservation squareAffordance
canonicalObserverAffordanceIncomparability =
  observer-affordance-incomparability
    sameApprovalDifferentAffordance
    sameAffordanceDifferentApproval

record ObserverAffordanceIncomparabilityBoundary : Set where
  constructor observer-affordance-incomparability-boundary
  field
    approvalImpliesAccessibility : Bool
    approvalImpliesAccessibilityIsFalse : approvalImpliesAccessibility ≡ false
    accessibilityImpliesApproval : Bool
    accessibilityImpliesApprovalIsFalse : accessibilityImpliesApproval ≡ false
    observerDisagreementProvesMaterialDifference : Bool
    observerDisagreementProvesMaterialDifferenceIsFalse :
      observerDisagreementProvesMaterialDifference ≡ false
    materialDifferenceSelectsNormativeAuthority : Bool
    materialDifferenceSelectsNormativeAuthorityIsFalse :
      materialDifferenceSelectsNormativeAuthority ≡ false

canonicalObserverAffordanceIncomparabilityBoundary :
  ObserverAffordanceIncomparabilityBoundary
canonicalObserverAffordanceIncomparabilityBoundary =
  observer-affordance-incomparability-boundary
    false refl false refl false refl false refl
