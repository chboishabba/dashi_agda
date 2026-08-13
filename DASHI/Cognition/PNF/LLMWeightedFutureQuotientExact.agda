module DASHI.Cognition.PNF.LLMWeightedFutureQuotientExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- WEIGHTED / PROBABILISTIC-NERODE-LIKE FUTURE QUOTIENT
--
-- The existing FutureObservationLanguageQuotientExact records which consumer
-- observations are reachable.  Language models additionally expose weights or
-- probabilities over continuations.  This module adds the exact algebraic
-- quotient at the level needed by the current repository without pretending
-- Nat-valued weights are calibrated probabilities.
------------------------------------------------------------------------

record WeightedFutureKernel
    (State Action Outcome : Set) : Set₁ where
  constructor weightedFutureKernel
  field
    weight : State → List Action → Outcome → Nat

open WeightedFutureKernel public

record WeightedFutureEquivalent
    {State Action Outcome : Set}
    (kernel : WeightedFutureKernel State Action Outcome)
    (left right : State) : Set₁ where
  constructor weightedFutureEquivalent
  field
    sameWeightedFuture :
      (actions : List Action) →
      (outcome : Outcome) →
      weight kernel left actions outcome ≡ weight kernel right actions outcome

open WeightedFutureEquivalent public

weightedFutureRefl :
  ∀ {State Action Outcome}
    {kernel : WeightedFutureKernel State Action Outcome}
    (state : State) →
  WeightedFutureEquivalent kernel state state
weightedFutureRefl state =
  weightedFutureEquivalent (λ actions outcome → refl)

weightedFutureSym :
  ∀ {State Action Outcome}
    {kernel : WeightedFutureKernel State Action Outcome}
    {left right : State} →
  WeightedFutureEquivalent kernel left right →
  WeightedFutureEquivalent kernel right left
weightedFutureSym equivalent =
  weightedFutureEquivalent λ actions outcome →
    sym (sameWeightedFuture equivalent actions outcome)

weightedFutureTrans :
  ∀ {State Action Outcome}
    {kernel : WeightedFutureKernel State Action Outcome}
    {left middle right : State} →
  WeightedFutureEquivalent kernel left middle →
  WeightedFutureEquivalent kernel middle right →
  WeightedFutureEquivalent kernel left right
weightedFutureTrans leftMiddle middleRight =
  weightedFutureEquivalent λ actions outcome →
    trans
      (sameWeightedFuture leftMiddle actions outcome)
      (sameWeightedFuture middleRight actions outcome)

------------------------------------------------------------------------
-- Universal safe-collapse criterion for weighted future kernels.
------------------------------------------------------------------------

record WeightedFutureSafeProjection
    {State Action Outcome Coarse : Set}
    (kernel : WeightedFutureKernel State Action Outcome)
    (coarsen : State → Coarse) : Set₁ where
  constructor weightedFutureSafeProjection
  field
    kernelContainedInWeightedFutureEquivalence :
      ∀ {left right} →
      coarsen left ≡ coarsen right →
      WeightedFutureEquivalent kernel left right

open WeightedFutureSafeProjection public

record ExactWeightedFutureSummary
    {State Action Outcome Coarse : Set}
    (kernel : WeightedFutureKernel State Action Outcome)
    (coarsen : State → Coarse) : Set₁ where
  constructor exactWeightedFutureSummary
  field
    summaryWeight : Coarse → List Action → Outcome → Nat
    summaryExact :
      (state : State) →
      (actions : List Action) →
      (outcome : Outcome) →
      weight kernel state actions outcome
      ≡ summaryWeight (coarsen state) actions outcome

open ExactWeightedFutureSummary public

exactSummaryCertifiesWeightedFutureSafety :
  ∀ {State Action Outcome Coarse}
    {kernel : WeightedFutureKernel State Action Outcome}
    {coarsen : State → Coarse} →
  ExactWeightedFutureSummary kernel coarsen →
  WeightedFutureSafeProjection kernel coarsen
exactSummaryCertifiesWeightedFutureSafety summary =
  weightedFutureSafeProjection certify
  where
    certify :
      ∀ {left right} →
      coarsen left ≡ coarsen right →
      WeightedFutureEquivalent kernel left right
    certify {left} {right} refl =
      weightedFutureEquivalent λ actions outcome →
        trans
          (summaryExact summary left actions outcome)
          (sym (summaryExact summary right actions outcome))

------------------------------------------------------------------------
-- Approximate weighted future sufficiency.
--
-- Rather than hard-code total variation/KL before real probability measures
-- are present, the distance is an explicit typed parameter.  This supports the
-- intended epsilon notion while preserving the current finite/Nat boundary.
------------------------------------------------------------------------

record ApproximateWeightedFutureEquivalent
    {State Action Outcome : Set}
    (kernel : WeightedFutureKernel State Action Outcome)
    (distance : Nat → Nat → Nat)
    (epsilon : Nat)
    (left right : State) : Set₁ where
  constructor approximateWeightedFutureEquivalent
  field
    weightedFutureWithinTolerance :
      (actions : List Action) →
      (outcome : Outcome) →
      distance
        (weight kernel left actions outcome)
        (weight kernel right actions outcome)
      ≤ epsilon

open ApproximateWeightedFutureEquivalent public

record ApproximateWeightedFutureSafeProjection
    {State Action Outcome Coarse : Set}
    (kernel : WeightedFutureKernel State Action Outcome)
    (distance : Nat → Nat → Nat)
    (epsilon : Nat)
    (coarsen : State → Coarse) : Set₁ where
  constructor approximateWeightedFutureSafeProjection
  field
    approximateKernelSafety :
      ∀ {left right} →
      coarsen left ≡ coarsen right →
      ApproximateWeightedFutureEquivalent
        kernel distance epsilon left right

open ApproximateWeightedFutureSafeProjection public

exactImpliesApproximateAtZero :
  ∀ {State Action Outcome}
    {kernel : WeightedFutureKernel State Action Outcome}
    (distance : Nat → Nat → Nat)
    (distanceReflexive : (n : Nat) → distance n n ≡ 0)
    {left right : State} →
  WeightedFutureEquivalent kernel left right →
  ApproximateWeightedFutureEquivalent kernel distance 0 left right
exactImpliesApproximateAtZero {kernel = kernel} distance distanceReflexive equivalent =
  approximateWeightedFutureEquivalent bound
  where
    bound :
      (actions : List _) →
      (outcome : _) →
      distance
        (weight kernel _ actions outcome)
        (weight kernel _ actions outcome)
      ≤ 0
    bound actions outcome with sameWeightedFuture equivalent actions outcome
    ... | refl with distanceReflexive (weight kernel _ actions outcome)
    ...   | refl = z≤n

------------------------------------------------------------------------
-- Boundary: this is a weighted kernel quotient.  A later analytic layer may
-- instantiate `distance` with total variation, Wasserstein, KL-derived bounds,
-- etc. only after genuine probability measures and their hypotheses exist.
------------------------------------------------------------------------
