module DASHI.Core.PolicyObserverFactorizationNaturalityExact where

------------------------------------------------------------------------
-- POLICY NATURALITY OVER FACTORIZED OBSERVATIONS
--
-- A coarse intervention policy can be transported to a finer observer only
-- through the declared forgetful map carried by FactorizedRefinement.  This
-- gives a theorem-bearing commuting square for selected actions:
--
--   fine observation --factor--> coarse observation
--          |                         |
--       fine policy              coarse policy
--          |                         |
--          +-------- same action ---+
--
-- This is deliberately weaker than dynamic/future safety.  Exact agreement
-- of selected actions does not prove that the coarse observation retained all
-- state needed to justify or evaluate those actions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.PolicyRelativeProjectionSafety as Policy
import DASHI.Core.TypedDependencyCore as Dependency

liftPolicyAlongFactorizedRefinement :
  ∀ {State Action Coarse Fine : Set}
    {coarse : Observer.Observer State Coarse}
    {fine : Observer.Observer State Fine} →
  Factorized.FactorizedRefinement coarse fine →
  Policy.CoarseInterventionPolicy Coarse Action →
  Policy.CoarseInterventionPolicy Fine Action
liftPolicyAlongFactorizedRefinement refinement policy =
  Policy.coarseInterventionPolicy
    (λ fineObservation →
      Policy.chooseAction policy (Factorized.factor refinement fineObservation))

liftedPolicyNaturality :
  ∀ {State Action Coarse Fine : Set}
    {coarse : Observer.Observer State Coarse}
    {fine : Observer.Observer State Fine}
    (refinement : Factorized.FactorizedRefinement coarse fine)
    (policy : Policy.CoarseInterventionPolicy Coarse Action)
    (state : State) →
  Policy.chooseAction
      (liftPolicyAlongFactorizedRefinement refinement policy)
      (fine state)
  ≡ Policy.chooseAction policy (coarse state)
liftedPolicyNaturality refinement policy state
  rewrite Factorized.factorizes refinement state = refl

liftedPolicyRespectsFineObservationEquality :
  ∀ {State Action Coarse Fine : Set}
    {coarse : Observer.Observer State Coarse}
    {fine : Observer.Observer State Fine}
    (refinement : Factorized.FactorizedRefinement coarse fine)
    (policy : Policy.CoarseInterventionPolicy Coarse Action)
    {left right : State} →
  fine left ≡ fine right →
  Policy.chooseAction
      (liftPolicyAlongFactorizedRefinement refinement policy)
      (fine left)
  ≡ Policy.chooseAction
      (liftPolicyAlongFactorizedRefinement refinement policy)
      (fine right)
liftedPolicyRespectsFineObservationEquality refinement policy same =
  cong
    (Policy.chooseAction
      (liftPolicyAlongFactorizedRefinement refinement policy))
    same

------------------------------------------------------------------------
-- Composition is coherent: lifting through two factorized refinement stages
-- selects the same action as lifting once through their composite factor.
------------------------------------------------------------------------

composedPolicyLiftNaturality :
  ∀ {State Action Coarse Middle Fine : Set}
    {coarse : Observer.Observer State Coarse}
    {middle : Observer.Observer State Middle}
    {fine : Observer.Observer State Fine}
    (first : Factorized.FactorizedRefinement coarse middle)
    (second : Factorized.FactorizedRefinement middle fine)
    (policy : Policy.CoarseInterventionPolicy Coarse Action)
    (fineObservation : Fine) →
  Policy.chooseAction
      (liftPolicyAlongFactorizedRefinement
        (Factorized.composeFactorizedRefinement first second)
        policy)
      fineObservation
  ≡ Policy.chooseAction
      (liftPolicyAlongFactorizedRefinement
        second
        (liftPolicyAlongFactorizedRefinement first policy))
      fineObservation
composedPolicyLiftNaturality first second policy fineObservation = refl

------------------------------------------------------------------------
-- If the fine observer is independently known dynamically safe, then the
-- lifted policy inherits policy-relative safety.  Factorized action naturality
-- does not manufacture the dynamic premise.
------------------------------------------------------------------------

fineDynamicSafetyImpliesLiftedPolicySafety :
  ∀ {State Action Coarse Fine : Set}
    {system : Dependency.DependentActionSystem State Action}
    {coarse : Observer.Observer State Coarse}
    {fine : Observer.Observer State Fine}
    (refinement : Factorized.FactorizedRefinement coarse fine)
    (policy : Policy.CoarseInterventionPolicy Coarse Action) →
  Dynamic.DynamicConsumerSafety system fine →
  Policy.PolicyRelativeSafety
    system
    fine
    (liftPolicyAlongFactorizedRefinement refinement policy)
fineDynamicSafetyImpliesLiftedPolicySafety refinement policy =
  Policy.dynamicSafetyImpliesPolicySafety
    (liftPolicyAlongFactorizedRefinement refinement policy)

record PolicyObserverFactorizationBoundary : Set where
  constructor policyObserverFactorizationBoundary
  field
    factorMapTransportsPolicy : Bool
    factorMapTransportsPolicyIsTrue : factorMapTransportsPolicy ≡ true
    policyLiftsCompose : Bool
    policyLiftsComposeIsTrue : policyLiftsCompose ≡ true
    actionNaturalityAloneProvesDynamicSafety : Bool
    actionNaturalityAloneProvesDynamicSafetyIsFalse :
      actionNaturalityAloneProvesDynamicSafety ≡ false
    actionNaturalityAloneProvesAuthorityLegitimacy : Bool
    actionNaturalityAloneProvesAuthorityLegitimacyIsFalse :
      actionNaturalityAloneProvesAuthorityLegitimacy ≡ false

canonicalPolicyObserverFactorizationBoundary :
  PolicyObserverFactorizationBoundary
canonicalPolicyObserverFactorizationBoundary =
  policyObserverFactorizationBoundary
    true refl
    true refl
    false refl
    false refl
