module DASHI.Governance.FederatedViabilityTransitionRegression where

open import DASHI.Core.Prelude

import DASHI.Governance.FederatedSubsidiarityGovernanceExact as Base
import DASHI.Governance.FederatedViabilityTransitionExact as V

reachablePathPreservesViability :
  ∀ {State : Set}
    {ts : Base.TransitionSystem State}
    {envelope : Base.ViabilityEnvelope State} →
  (preservation : V.ViabilityPreservingTransition ts envelope) →
  ∀ {source target} →
  Base.Reachable ts source target →
  Base.Viable envelope source →
  Base.Viable envelope target
reachablePathPreservesViability =
  V.reachablePreservesViability

transitionKindAloneDoesNotGuaranteeViability :
  V.transitionKindAloneGuaranteesViability
    V.canonicalViabilityTransitionBoundary
  ≡ false
transitionKindAloneDoesNotGuaranteeViability = refl

reachabilityAloneDoesNotMeanImprovement :
  V.reachabilityAloneMeansImprovement
    V.canonicalViabilityTransitionBoundary
  ≡ false
reachabilityAloneDoesNotMeanImprovement = refl

preservationWitnessRequired :
  V.viabilityPreservationWitnessRequired
    V.canonicalViabilityTransitionBoundary
  ≡ true
preservationWitnessRequired = refl
