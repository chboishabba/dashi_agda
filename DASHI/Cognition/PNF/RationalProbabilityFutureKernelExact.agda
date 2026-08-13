module DASHI.Cognition.PNF.RationalProbabilityFutureKernelExact where

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; ½; _+_; _-_; _*_; ∣_∣; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Analysis.CanonicalRationalMetric as Metric

------------------------------------------------------------------------
-- NORMALIZED RATIONAL PROBABILITY KERNELS
--
-- Unlike the earlier Nat-weight surface, every binary distribution here is a
-- genuine normalized rational probability vector: both masses are nonnegative
-- and sum exactly to one.
------------------------------------------------------------------------

record BinaryProbability : Set where
  constructor binaryProbability
  field
    falseMass trueMass : ℚ
    falseNonnegative : 0ℚ ≤ falseMass
    trueNonnegative : 0ℚ ≤ trueMass
    normalized : falseMass + trueMass ≡ 1ℚ

open BinaryProbability public

record RationalProbabilityFutureKernel (State Action : Set) : Set₁ where
  constructor rationalProbabilityFutureKernel
  field
    distribution : State → List Action → BinaryProbability

open RationalProbabilityFutureKernel public

------------------------------------------------------------------------
-- Total variation for a binary law: 1/2 times the L1 difference.
------------------------------------------------------------------------

totalVariation : BinaryProbability → BinaryProbability → ℚ
totalVariation left right =
  ½ *
    (∣ falseMass left - falseMass right ∣
      + ∣ trueMass left - trueMass right ∣)

totalVariationRefl : (probability : BinaryProbability) →
  totalVariation probability probability ≡ 0ℚ
totalVariationRefl probability
  rewrite Metric.subSelfℚ (falseMass probability)
        | Metric.subSelfℚ (trueMass probability)
        | Metric.absZeroℚ =
  solve-∀

halfNonnegative : 0ℚ ≤ ½
halfNonnegative = Metric.halfNonnegative

private
  halfReassociate : ∀ a b c d →
    ½ * ((a + b) + (c + d))
    ≡ (½ * (a + c)) + (½ * (b + d))
  halfReassociate = solve-∀

totalVariationTriangle : (left middle right : BinaryProbability) →
  totalVariation left right
  ≤ totalVariation left middle + totalVariation middle right
totalVariationTriangle left middle right =
  begin
    ½ *
      (∣ falseMass left - falseMass right ∣
        + ∣ trueMass left - trueMass right ∣)
      ≤⟨ ℚₚ.*-monoˡ-≤-nonNeg ½
          (ℚₚ.+-mono-≤
            (Metric.absDifferenceTriangle
              (falseMass left) (falseMass middle) (falseMass right))
            (Metric.absDifferenceTriangle
              (trueMass left) (trueMass middle) (trueMass right))) ⟩
    ½ *
      ((∣ falseMass left - falseMass middle ∣
          + ∣ falseMass middle - falseMass right ∣)
        +
       (∣ trueMass left - trueMass middle ∣
          + ∣ trueMass middle - trueMass right ∣))
      ≡⟨ halfReassociate
          ∣ falseMass left - falseMass middle ∣
          ∣ falseMass middle - falseMass right ∣
          ∣ trueMass left - trueMass middle ∣
          ∣ trueMass middle - trueMass right ∣ ⟩
    totalVariation left middle + totalVariation middle right
    ∎
  where
    open ℚₚ.≤-Reasoning
    instance
      halfNN : NonNegative ½
      halfNN = nonNegative halfNonnegative

record ProbabilityFutureEquivalent
    {State Action : Set}
    (kernel : RationalProbabilityFutureKernel State Action)
    (left right : State) : Set₁ where
  constructor probabilityFutureEquivalent
  field
    sameDistributionForEveryTrace :
      (actions : List Action) →
      distribution kernel left actions ≡ distribution kernel right actions

open ProbabilityFutureEquivalent public

record ApproxProbabilityFutureEquivalent
    {State Action : Set}
    (kernel : RationalProbabilityFutureKernel State Action)
    (epsilon : ℚ)
    (left right : State) : Set₁ where
  constructor approxProbabilityFutureEquivalent
  field
    futureTVBound :
      (actions : List Action) →
      totalVariation
        (distribution kernel left actions)
        (distribution kernel right actions)
      ≤ epsilon

open ApproxProbabilityFutureEquivalent public

------------------------------------------------------------------------
-- Quantitative composition: epsilon errors add.
------------------------------------------------------------------------

approxFutureErrorComposition :
  ∀ {State Action}
    {kernel : RationalProbabilityFutureKernel State Action}
    {epsilon₁ epsilon₂ : ℚ}
    {left middle right : State} →
  ApproxProbabilityFutureEquivalent kernel epsilon₁ left middle →
  ApproxProbabilityFutureEquivalent kernel epsilon₂ middle right →
  ApproxProbabilityFutureEquivalent kernel (epsilon₁ + epsilon₂) left right
approxFutureErrorComposition {kernel = kernel} leftMiddle middleRight =
  approxProbabilityFutureEquivalent λ actions →
    ℚₚ.≤-trans
      (totalVariationTriangle
        (distribution kernel _ actions)
        (distribution kernel _ actions)
        (distribution kernel _ actions))
      (ℚₚ.+-mono-≤
        (futureTVBound leftMiddle actions)
        (futureTVBound middleRight actions))

------------------------------------------------------------------------
-- Data processing under an explicitly non-expansive stochastic/post-processing
-- map.  This is the exact finite total-variation form of the PNF requirement.
------------------------------------------------------------------------

record TVNonExpansivePostprocess : Set₁ where
  constructor tvNonExpansivePostprocess
  field
    postprocess : BinaryProbability → BinaryProbability
    tvNonExpansive : (left right : BinaryProbability) →
      totalVariation (postprocess left) (postprocess right)
      ≤ totalVariation left right

open TVNonExpansivePostprocess public

postprocessedKernel :
  ∀ {State Action} →
  TVNonExpansivePostprocess →
  RationalProbabilityFutureKernel State Action →
  RationalProbabilityFutureKernel State Action
postprocessedKernel processor kernel =
  rationalProbabilityFutureKernel λ state actions →
    postprocess processor (distribution kernel state actions)

probabilityDataProcessing :
  ∀ {State Action}
    {kernel : RationalProbabilityFutureKernel State Action}
    {epsilon : ℚ}
    {left right : State}
    (processor : TVNonExpansivePostprocess) →
  ApproxProbabilityFutureEquivalent kernel epsilon left right →
  ApproxProbabilityFutureEquivalent
    (postprocessedKernel processor kernel) epsilon left right
probabilityDataProcessing {kernel = kernel} processor approximate =
  approxProbabilityFutureEquivalent λ actions →
    ℚₚ.≤-trans
      (tvNonExpansive processor
        (distribution kernel _ actions)
        (distribution kernel _ actions))
      (futureTVBound approximate actions)

------------------------------------------------------------------------
-- Boundary: this is genuine finite rational probability semantics.  It is not
-- yet a sigma-additive probability measure on an infinite token/trace space.
------------------------------------------------------------------------
