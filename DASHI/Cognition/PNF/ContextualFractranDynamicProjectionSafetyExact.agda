module DASHI.Cognition.PNF.ContextualFractranDynamicProjectionSafetyExact where

open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.FutureObservationalRefinement as Future
import DASHI.Core.PolicyRelativeProjectionSafety as Policy
import DASHI.Core.PluralConsumerProjectionSafety as Plural
import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Cognition.PNF.ContextualFractranFibreRestrictionExact as Fibre
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.SSPTritCarrier as Trit

------------------------------------------------------------------------
-- Same current requested trit is not automatically a safe execution quotient.
-- A consumer/action system must prove trace congruence.  Safety for one prime
-- or one policy is not promoted to every other query/prime consumer.
------------------------------------------------------------------------

record ContextualDynamicSafety (Action : Set) : Set₁ where
  constructor contextualDynamicSafety
  field
    system :
      Dependency.DependentActionSystem Context.ContextualValuation Action
    requestedPrime : Signed.SSPPrime
    dynamicSafety :
      Dynamic.DynamicConsumerSafety
        system
        (Fibre.projectRequestedPrime requestedPrime)

open ContextualDynamicSafety public

currentEqualityPromotesToFutureOnlyWithSafety :
  ∀ {Action}
    (receipt : ContextualDynamicSafety Action) →
    {left right : Context.ContextualValuation} →
    Fibre.projectRequestedPrime (requestedPrime receipt) left
      ≡ Fibre.projectRequestedPrime (requestedPrime receipt) right →
    Future.FutureEquivalent
      (system receipt)
      (Fibre.projectRequestedPrime (requestedPrime receipt))
      left right
currentEqualityPromotesToFutureOnlyWithSafety receipt =
  Future.dynamicSafetyExactlyPromotesCurrentToFuture (dynamicSafety receipt)

record ContextualPolicySafety (Action : Set) : Set₁ where
  constructor contextualPolicySafety
  field
    dynamic : ContextualDynamicSafety Action
    policy : Policy.CoarseInterventionPolicy Trit.SSPTrit Action
    policySafety :
      Policy.PolicyRelativeSafety
        (system dynamic)
        (Fibre.projectRequestedPrime (requestedPrime dynamic))
        policy

open ContextualPolicySafety public

contextualPrimeConsumerFamily :
  ∀ {Action : Set} →
  Dependency.DependentActionSystem Context.ContextualValuation Action →
  Plural.ConsumerProjectionFamily
    Context.ContextualValuation Action Signed.SSPPrime Trit.SSPTrit
contextualPrimeConsumerFamily system =
  Plural.consumerProjectionFamily
    system
    (λ prime valuation → Fibre.projectRequestedPrime prime valuation)

record ContextualProjectionSafetyBoundary : Set where
  constructor contextualProjectionSafetyBoundary
  field
    sameCurrentTritAutomaticallyFutureEquivalent : Bool
    dynamicCongruenceCanPromoteCurrentToFuture : Bool
    safetyForOnePrimeImpliesSafetyForEveryPrime : Bool
    safetyForOnePolicyImpliesUnrestrictedDynamicSafety : Bool

canonicalContextualProjectionSafetyBoundary : ContextualProjectionSafetyBoundary
canonicalContextualProjectionSafetyBoundary =
  contextualProjectionSafetyBoundary false true false false
