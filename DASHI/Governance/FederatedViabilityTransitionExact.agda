module DASHI.Governance.FederatedViabilityTransitionExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.FederatedSubsidiarityGovernanceExact as Base

------------------------------------------------------------------------
-- Witness-gated viability preservation across gradual transition.
------------------------------------------------------------------------

record ViabilityPreservingTransition
  {State : Set}
  (transitionSystem : Base.TransitionSystem State)
  (envelope : Base.ViabilityEnvelope State) : Set₁ where
  field
    preservesStep :
      ∀ {kind source target} →
      Base.step transitionSystem kind source target →
      Base.Viable envelope source →
      Base.Viable envelope target

open ViabilityPreservingTransition public

reachablePreservesViability :
  ∀ {State : Set}
    {transitionSystem : Base.TransitionSystem State}
    {envelope : Base.ViabilityEnvelope State} →
  (preservation : ViabilityPreservingTransition transitionSystem envelope) →
  ∀ {source target} →
  Base.Reachable transitionSystem source target →
  Base.Viable envelope source →
  Base.Viable envelope target
reachablePreservesViability preservation Base.reachableRefl viable =
  viable
reachablePreservesViability
  preservation
  (Base.reachableByStep stepWitness)
  viable =
    preservesStep preservation stepWitness viable
reachablePreservesViability
  preservation
  (Base.reachableTrans sourceToMiddle middleToTarget)
  viable =
    reachablePreservesViability
      preservation
      middleToTarget
      (reachablePreservesViability preservation sourceToMiddle viable)

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ViabilityTransitionBoundary : Set where
  constructor viabilityTransitionBoundary
  field
    transitionKindAloneGuaranteesViability : Bool
    reachabilityAloneMeansImprovement : Bool
    viabilityPreservationWitnessRequired : Bool
    governanceViabilityImpliesEcologicalViability : Bool
    ecologicalViabilityImpliesBasicNeedsAccessible : Bool
    theoremCreatesEmpiricalTransitionPlan : Bool

open ViabilityTransitionBoundary public

canonicalViabilityTransitionBoundary : ViabilityTransitionBoundary
canonicalViabilityTransitionBoundary =
  viabilityTransitionBoundary
    false
    false
    true
    false
    false
    false

canonicalFederatedViabilityTransitionReceipt :
  GenericReceipt.GenericReceipt
canonicalFederatedViabilityTransitionReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "witness-gated federated viability transition"
    "DASHI.Governance.FederatedViabilityTransitionExact"
    "canonicalViabilityTransitionBoundary"
    "proves by induction on reflexive-transitive reachability that an independently supplied viability envelope is preserved when every admitted transition step carries a viability-preservation witness"
    "transition kind and reachability alone imply neither improvement nor viability, the viability dimensions remain independent, and no empirical transition programme is generated"
    "agda -i . DASHI/Governance/FederatedViabilityTransitionRegression.agda"
