module DASHI.Cognition.PNF.RationalProbabilityFutureQuotientExact where

open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)
import Data.Rational.Properties as ℚₚ

import DASHI.Cognition.PNF.RationalProbabilityFutureKernelExact as Probability

------------------------------------------------------------------------
-- CANONICAL QUOTIENT LAWS FOR NORMALIZED RATIONAL FUTURE KERNELS
------------------------------------------------------------------------

probabilityFutureRefl :
  ∀ {State Action}
    {kernel : Probability.RationalProbabilityFutureKernel State Action}
    (state : State) →
  Probability.ProbabilityFutureEquivalent kernel state state
probabilityFutureRefl state =
  Probability.probabilityFutureEquivalent (λ actions → refl)

probabilityFutureSym :
  ∀ {State Action}
    {kernel : Probability.RationalProbabilityFutureKernel State Action}
    {left right : State} →
  Probability.ProbabilityFutureEquivalent kernel left right →
  Probability.ProbabilityFutureEquivalent kernel right left
probabilityFutureSym equivalent =
  Probability.probabilityFutureEquivalent λ actions →
    sym (Probability.sameDistributionForEveryTrace equivalent actions)

probabilityFutureTrans :
  ∀ {State Action}
    {kernel : Probability.RationalProbabilityFutureKernel State Action}
    {left middle right : State} →
  Probability.ProbabilityFutureEquivalent kernel left middle →
  Probability.ProbabilityFutureEquivalent kernel middle right →
  Probability.ProbabilityFutureEquivalent kernel left right
probabilityFutureTrans leftMiddle middleRight =
  Probability.probabilityFutureEquivalent λ actions →
    trans
      (Probability.sameDistributionForEveryTrace leftMiddle actions)
      (Probability.sameDistributionForEveryTrace middleRight actions)

record ProbabilityFutureSafeProjection
    {State Action Coarse : Set}
    (kernel : Probability.RationalProbabilityFutureKernel State Action)
    (coarsen : State → Coarse) : Set₁ where
  constructor probabilityFutureSafeProjection
  field
    kernelContainedInProbabilityFutureEquivalence :
      ∀ {left right} →
      coarsen left ≡ coarsen right →
      Probability.ProbabilityFutureEquivalent kernel left right

open ProbabilityFutureSafeProjection public

record ExactProbabilityFutureSummary
    {State Action Coarse : Set}
    (kernel : Probability.RationalProbabilityFutureKernel State Action)
    (coarsen : State → Coarse) : Set₁ where
  constructor exactProbabilityFutureSummary
  field
    summaryDistribution :
      Coarse → List Action → Probability.BinaryProbability
    summaryExact :
      (state : State) →
      (actions : List Action) →
      Probability.distribution kernel state actions
      ≡ summaryDistribution (coarsen state) actions

open ExactProbabilityFutureSummary public

exactSummaryCertifiesProbabilityFutureSafety :
  ∀ {State Action Coarse}
    {kernel : Probability.RationalProbabilityFutureKernel State Action}
    {coarsen : State → Coarse} →
  ExactProbabilityFutureSummary kernel coarsen →
  ProbabilityFutureSafeProjection kernel coarsen
exactSummaryCertifiesProbabilityFutureSafety summary =
  probabilityFutureSafeProjection certify
  where
    certify :
      ∀ {left right} →
      coarsen left ≡ coarsen right →
      Probability.ProbabilityFutureEquivalent kernel left right
    certify {left} {right} refl =
      Probability.probabilityFutureEquivalent λ actions →
        trans
          (summaryExact summary left actions)
          (sym (summaryExact summary right actions))

record ApproxProbabilityFutureSafeProjection
    {State Action Coarse : Set}
    (kernel : Probability.RationalProbabilityFutureKernel State Action)
    (epsilon : ℚ)
    (coarsen : State → Coarse) : Set₁ where
  constructor approxProbabilityFutureSafeProjection
  field
    approximateKernelSafety :
      ∀ {left right} →
      coarsen left ≡ coarsen right →
      Probability.ApproxProbabilityFutureEquivalent kernel epsilon left right

open ApproxProbabilityFutureSafeProjection public

exactImpliesApproximateAtZero :
  ∀ {State Action}
    {kernel : Probability.RationalProbabilityFutureKernel State Action}
    {left right : State} →
  Probability.ProbabilityFutureEquivalent kernel left right →
  Probability.ApproxProbabilityFutureEquivalent kernel 0ℚ left right
exactImpliesApproximateAtZero {kernel = kernel} {left = left} exact =
  Probability.approxProbabilityFutureEquivalent bound
  where
    bound :
      (actions : List _) →
      Probability.totalVariation
        (Probability.distribution kernel left actions)
        (Probability.distribution kernel _ actions)
      ≤ 0ℚ
    bound actions
      with Probability.sameDistributionForEveryTrace exact actions
    ... | refl
      rewrite Probability.totalVariationRefl
        (Probability.distribution kernel left actions) =
      ℚₚ.≤-refl

toleranceMonotone :
  ∀ {State Action}
    {kernel : Probability.RationalProbabilityFutureKernel State Action}
    {epsilon epsilon′ : ℚ}
    {left right : State} →
  epsilon ≤ epsilon′ →
  Probability.ApproxProbabilityFutureEquivalent kernel epsilon left right →
  Probability.ApproxProbabilityFutureEquivalent kernel epsilon′ left right
toleranceMonotone epsilon≤epsilon′ approximate =
  Probability.approxProbabilityFutureEquivalent λ actions →
    ℚₚ.≤-trans
      (Probability.futureTVBound approximate actions)
      epsilon≤epsilon′

safeProjectionToleranceMonotone :
  ∀ {State Action Coarse}
    {kernel : Probability.RationalProbabilityFutureKernel State Action}
    {epsilon epsilon′ : ℚ}
    {coarsen : State → Coarse} →
  epsilon ≤ epsilon′ →
  ApproxProbabilityFutureSafeProjection kernel epsilon coarsen →
  ApproxProbabilityFutureSafeProjection kernel epsilon′ coarsen
safeProjectionToleranceMonotone epsilon≤epsilon′ safe =
  approxProbabilityFutureSafeProjection λ equality →
    toleranceMonotone epsilon≤epsilon′
      (approximateKernelSafety safe equality)

------------------------------------------------------------------------
-- This is the normalized probabilistic counterpart of
-- `ker(coarsen) subseteq future-equivalence`.
------------------------------------------------------------------------
