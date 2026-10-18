module DASHI.Mathematics.Complexity.PolynomialClassicalObserverExact where

------------------------------------------------------------------------
-- SIZED POLYNOMIAL CLASSICAL OBSERVERS
--
-- A candidate observer for P-vs-NP must carry more than an extensional map.
-- This owner records:
--
--   * the representation algorithm;
--   * an input-size metric;
--   * representation-size, construction-cost and recovery-cost envelopes;
--   * polynomial bounds for all three envelopes;
--   * a downstream decision algorithm and pointwise correctness.
--
-- The object does not claim that all polynomial-time algorithms factor through
-- one such observer family.  That coverage theorem remains the research wall.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)

import DASHI.Core.EfficientRecoverableQuotientExact as ERQ
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PolynomialFactorisationCostExact as Factor

record LengthIndexedEnvelope
    {Word : Set}
    (inputLength : Word → Nat)
    (measured : Word → Nat) : Set where
  field
    envelope : Nat → Nat
    dominates :
      (word : Word) →
      measured word ≤ envelope (inputLength word)
    polynomial :
      ERQ.PolynomialBound envelope

open LengthIndexedEnvelope public

record PolynomialClassicalObserver
    {Word : Set}
    (cost : PR.PolynomialCostModel Word)
    (consumer : Word → Bool) : Set₁ where
  field
    inputLength : Word → Nat

    representation : Word → Word
    representationSize : Word → Nat
    constructionCost : Word → Nat

    recoverDecision : Word → Bool
    recoveryCost : Word → Nat

    representationSizeBound :
      LengthIndexedEnvelope inputLength representationSize
    constructionCostBound :
      LengthIndexedEnvelope inputLength constructionCost
    recoveryCostBound :
      LengthIndexedEnvelope inputLength recoveryCost

    representationPolynomial :
      PR.polynomialTimeMap cost representation
    recoveryPolynomial :
      PR.polynomialTimeDecider cost recoverDecision

    consumerFactors :
      (word : Word) →
      consumer word ≡ recoverDecision (representation word)

open PolynomialClassicalObserver public

observerToCostAwareFactorisation :
  ∀ {Word} {cost : PR.PolynomialCostModel Word}
    {consumer : Word → Bool} →
  PolynomialClassicalObserver cost consumer →
  Factor.CostAwareDecisionFactorisation cost consumer
observerToCostAwareFactorisation observer = record
  { Factor.observe = representation observer
  ; Factor.consumeObserved = recoverDecision observer
  ; Factor.factorisationCorrect = consumerFactors observer
  ; Factor.observerPolynomial = representationPolynomial observer
  ; Factor.observedConsumerPolynomial = recoveryPolynomial observer
  }

observerGivesPolynomialDecision :
  ∀ {Word} {cost : PR.PolynomialCostModel Word}
    (extensionality : Factor.PolynomialDeciderExtensionality cost)
    {consumer : Word → Bool} →
  PolynomialClassicalObserver cost consumer →
  PR.polynomialTimeDecider cost consumer
observerGivesPolynomialDecision extensionality observer =
  Factor.costAwareFactorisationGivesPolynomialDecision
    extensionality
    (observerToCostAwareFactorisation observer)
