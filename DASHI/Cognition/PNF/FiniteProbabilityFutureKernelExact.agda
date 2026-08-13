module DASHI.Cognition.PNF.FiniteProbabilityFutureKernelExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- FINITE PROBABILITY / MARKOV-KERNEL FUTURE EQUIVALENCE
--
-- This upgrades the Nat-weight precursor to normalized finite rational
-- probability distributions with a shared denominator.  The analytic real-
-- probability layer can later embed these exact rational distributions.
------------------------------------------------------------------------

record BinaryProbability (denominator : Nat) : Set where
  constructor binaryProbability
  field
    falseMass : Nat
    trueMass : Nat
    normalized : falseMass + trueMass ≡ denominator

open BinaryProbability public

record ProbabilityFutureKernel
    (State Action : Set)
    (denominator : Nat) : Set₁ where
  constructor probabilityFutureKernel
  field
    distribution : State → List Action → BinaryProbability denominator

open ProbabilityFutureKernel public

record ProbabilityFutureEquivalent
    {State Action : Set}
    {denominator : Nat}
    (kernel : ProbabilityFutureKernel State Action denominator)
    (left right : State) : Set₁ where
  constructor probabilityFutureEquivalent
  field
    sameFutureDistribution :
      (actions : List Action) →
      distribution kernel left actions ≡ distribution kernel right actions

open ProbabilityFutureEquivalent public

probabilityFutureRefl :
  ∀ {State Action denominator}
    {kernel : ProbabilityFutureKernel State Action denominator}
    (state : State) →
  ProbabilityFutureEquivalent kernel state state
probabilityFutureRefl state =
  probabilityFutureEquivalent (λ actions → refl)

probabilityFutureSym :
  ∀ {State Action denominator}
    {kernel : ProbabilityFutureKernel State Action denominator}
    {left right : State} →
  ProbabilityFutureEquivalent kernel left right →
  ProbabilityFutureEquivalent kernel right left
probabilityFutureSym equivalent =
  probabilityFutureEquivalent λ actions →
    sym (sameFutureDistribution equivalent actions)

probabilityFutureTrans :
  ∀ {State Action denominator}
    {kernel : ProbabilityFutureKernel State Action denominator}
    {left middle right : State} →
  ProbabilityFutureEquivalent kernel left middle →
  ProbabilityFutureEquivalent kernel middle right →
  ProbabilityFutureEquivalent kernel left right
probabilityFutureTrans leftMiddle middleRight =
  probabilityFutureEquivalent λ actions →
    trans
      (sameFutureDistribution leftMiddle actions)
      (sameFutureDistribution middleRight actions)

------------------------------------------------------------------------
-- Quantitative approximate equivalence.  The metric is explicit and carries
-- exactly the laws needed for epsilon-error composition.
------------------------------------------------------------------------

record ProbabilityMetric (denominator : Nat) : Set₁ where
  constructor probabilityMetric
  field
    distance : BinaryProbability denominator → BinaryProbability denominator → Nat
    distanceReflexive :
      (p : BinaryProbability denominator) → distance p p ≡ 0
    triangle :
      (p q r : BinaryProbability denominator) →
      distance p r ≤ distance p q + distance q r

open ProbabilityMetric public

record ApproxProbabilityFutureEquivalent
    {State Action : Set}
    {denominator : Nat}
    (kernel : ProbabilityFutureKernel State Action denominator)
    (metric : ProbabilityMetric denominator)
    (epsilon : Nat)
    (left right : State) : Set₁ where
  constructor approxProbabilityFutureEquivalent
  field
    futureDistanceBound :
      (actions : List Action) →
      distance metric
        (distribution kernel left actions)
        (distribution kernel right actions)
      ≤ epsilon

open ApproxProbabilityFutureEquivalent public

approxProbabilityFutureTrans :
  ∀ {State Action denominator}
    {kernel : ProbabilityFutureKernel State Action denominator}
    {metric : ProbabilityMetric denominator}
    {epsilon₁ epsilon₂ : Nat}
    {left middle right : State} →
  ApproxProbabilityFutureEquivalent kernel metric epsilon₁ left middle →
  ApproxProbabilityFutureEquivalent kernel metric epsilon₂ middle right →
  ApproxProbabilityFutureEquivalent
    kernel metric (epsilon₁ + epsilon₂) left right
approxProbabilityFutureTrans {kernel = kernel} {metric = metric}
  leftMiddle middleRight =
  approxProbabilityFutureEquivalent λ actions →
    ≤-trans
      (triangle metric
        (distribution kernel _ actions)
        (distribution kernel _ actions)
        (distribution kernel _ actions))
      (+-mono-≤
        (futureDistanceBound leftMiddle actions)
        (futureDistanceBound middleRight actions))

------------------------------------------------------------------------
-- Data processing.  A Markov/post-processing map may only improve an epsilon
-- guarantee when it is non-expansive for the declared probability metric.
------------------------------------------------------------------------

record NonExpansiveProbabilityPostprocess
    {denominator : Nat}
    (metric : ProbabilityMetric denominator) : Set₁ where
  constructor nonExpansiveProbabilityPostprocess
  field
    postprocess : BinaryProbability denominator → BinaryProbability denominator
    nonExpansive :
      (left right : BinaryProbability denominator) →
      distance metric (postprocess left) (postprocess right)
      ≤ distance metric left right

open NonExpansiveProbabilityPostprocess public

postprocessedKernel :
  ∀ {State Action denominator}
    {metric : ProbabilityMetric denominator} →
  NonExpansiveProbabilityPostprocess metric →
  ProbabilityFutureKernel State Action denominator →
  ProbabilityFutureKernel State Action denominator
postprocessedKernel processor kernel =
  probabilityFutureKernel λ state actions →
    postprocess processor (distribution kernel state actions)

probabilityDataProcessing :
  ∀ {State Action denominator}
    {kernel : ProbabilityFutureKernel State Action denominator}
    {metric : ProbabilityMetric denominator}
    {epsilon : Nat}
    {left right : State}
    (processor : NonExpansiveProbabilityPostprocess metric) →
  ApproxProbabilityFutureEquivalent kernel metric epsilon left right →
  ApproxProbabilityFutureEquivalent
    (postprocessedKernel processor kernel) metric epsilon left right
probabilityDataProcessing {kernel = kernel} {metric = metric}
  processor approximate =
  approxProbabilityFutureEquivalent λ actions →
    ≤-trans
      (nonExpansive processor
        (distribution kernel _ actions)
        (distribution kernel _ actions))
      (futureDistanceBound approximate actions)

------------------------------------------------------------------------
-- Boundary: `BinaryProbability denominator` is an exact finite rational
-- distribution, not yet a sigma-additive measure on an infinite outcome space.
------------------------------------------------------------------------
