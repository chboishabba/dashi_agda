module DASHI.Cognition.PNF.ContextualFractranGovernedConsumerTransitionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Core.ConsumerIndexedGovernedTransitionExact as Governed
import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Cognition.PNF.ContextualFractranFibreRestrictionExact as Fibre
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.SSPTritCarrier as Trit

------------------------------------------------------------------------
-- A requested prime can serve as a consumer index, but quotient safety still
-- has to preserve action transitions, observations and authority separately.
-- This gives a stronger future-safe notion than same current trit.
------------------------------------------------------------------------

ContextualPrimeConsumer : Set
ContextualPrimeConsumer = Signed.SSPPrime

record ContextualGovernedSystem (Action : Set) : Set₁ where
  constructor contextualGovernedSystem
  field
    governed :
      Governed.ConsumerIndexedGovernedTransition
        Context.ContextualValuation
        Action
        ContextualPrimeConsumer
        Trit.SSPTrit
    observationIsRequestedPrime :
      (prime : ContextualPrimeConsumer) →
      (valuation : Context.ContextualValuation) →
      Governed.observe governed prime valuation
      ≡ Fibre.projectRequestedPrime prime valuation

open ContextualGovernedSystem public

record ContextualSafeAbstraction (Action Coarse : Set) : Set₁ where
  constructor contextualSafeAbstraction
  field
    system : ContextualGovernedSystem Action
    project : Context.ContextualValuation → Coarse
    abstraction :
      Governed.ConsumerSafeAbstraction (governed system) project

open ContextualSafeAbstraction public

sameCoarseStatePreservesRequestedPrimeFuture :
  ∀ {Action Coarse}
    (safe : ContextualSafeAbstraction Action Coarse) →
    (prime : ContextualPrimeConsumer) →
    (depth : Nat) →
    {left right : Context.ContextualValuation} →
    project safe left ≡ project safe right →
    Governed.FutureEquivalent
      (governed (system safe)) prime depth left right
sameCoarseStatePreservesRequestedPrimeFuture safe prime depth =
  Governed.sameProjectionFutureEquivalent (abstraction safe) prime depth

record GovernedConsumerBoundary : Set where
  constructor governedConsumerBoundary
  field
    sameCurrentTritIsEnoughForGovernedAbstraction : Bool
    actionCommutationMustBeProved : Bool
    observationDescentMustBeProved : Bool
    authorityDescentMustBeProvedSeparately : Bool
    safeAbstractionPreservesDeclaredFiniteFuture : Bool

canonicalGovernedConsumerBoundary : GovernedConsumerBoundary
canonicalGovernedConsumerBoundary =
  governedConsumerBoundary false true true true true
