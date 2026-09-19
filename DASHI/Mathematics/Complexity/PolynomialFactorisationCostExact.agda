module DASHI.Mathematics.Complexity.PolynomialFactorisationCostExact where

------------------------------------------------------------------------
-- COST-AWARE FACTORISATION
--
-- Extensional factorisation alone does not imply efficiency.  This module
-- adds exactly the missing complexity premise:
--
--   F = Fbar o observer
--   observer is polynomial-time
--   Fbar is polynomial-time
--   polynomial-time deciders are stable under pointwise equality
--   -------------------------------------------------------------
--   F is polynomial-time.
--
-- No complexity lower bound or P = NP consequence is manufactured.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR

record PolynomialDeciderExtensionality
    {Word : Set}
    (cost : PR.PolynomialCostModel Word) : Set₁ where
  field
    polynomialDeciderRespectsPointwiseEquality :
      ∀ {left right : Word → Bool} →
      ((word : Word) → left word ≡ right word) →
      PR.polynomialTimeDecider cost left →
      PR.polynomialTimeDecider cost right

open PolynomialDeciderExtensionality public

record CostAwareDecisionFactorisation
    {Word : Set}
    (cost : PR.PolynomialCostModel Word)
    (consumer : Word → Bool) : Set₁ where
  field
    observe : Word → Word
    consumeObserved : Word → Bool
    factorisationCorrect :
      (word : Word) →
      consumer word ≡ consumeObserved (observe word)
    observerPolynomial :
      PR.polynomialTimeMap cost observe
    observedConsumerPolynomial :
      PR.polynomialTimeDecider cost consumeObserved

open CostAwareDecisionFactorisation public

factorisationCompositePolynomial :
  ∀ {Word} {cost : PR.PolynomialCostModel Word}
    {consumer : Word → Bool} →
  CostAwareDecisionFactorisation cost consumer →
  PR.polynomialTimeDecider cost
    (λ word →
      consumeObserved
        {cost = cost}
        {consumer = consumer}
        _ (observe
          {cost = cost}
          {consumer = consumer}
          _ word))
factorisationCompositePolynomial {cost = cost} factorisation =
  PR.deciderClosedUnderPrecomposition cost
    (observe factorisation)
    (consumeObserved factorisation)
    (observerPolynomial factorisation)
    (observedConsumerPolynomial factorisation)

costAwareFactorisationGivesPolynomialDecision :
  ∀ {Word} {cost : PR.PolynomialCostModel Word}
    (extensionality : PolynomialDeciderExtensionality cost)
    {consumer : Word → Bool} →
  CostAwareDecisionFactorisation cost consumer →
  PR.polynomialTimeDecider cost consumer
costAwareFactorisationGivesPolynomialDecision
    extensionality factorisation =
  polynomialDeciderRespectsPointwiseEquality extensionality
    (λ word → sym (factorisationCorrect factorisation word))
    (factorisationCompositePolynomial factorisation)

record PolynomialFactorisationBoundary : Set where
  constructor polynomial-factorisation-boundary
  field
    extensionalFactorisationAloneImpliesPolynomialTime : Agda.Builtin.Bool.Bool
    observerCostRequired : Agda.Builtin.Bool.Bool
    downstreamCostRequired : Agda.Builtin.Bool.Bool
    equalityTransportRequiredByCurrentCostInterface : Agda.Builtin.Bool.Bool
    costAwareCompilerConstructed : Agda.Builtin.Bool.Bool

canonicalPolynomialFactorisationBoundary :
  PolynomialFactorisationBoundary
canonicalPolynomialFactorisationBoundary =
  polynomial-factorisation-boundary
    Agda.Builtin.Bool.false
    Agda.Builtin.Bool.true
    Agda.Builtin.Bool.true
    Agda.Builtin.Bool.true
    Agda.Builtin.Bool.true
