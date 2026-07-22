module DASHI.Cognition.CognitiveObservableDistributions where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.List using (length)

import DASHI.Cognition.DashiCognitiveSystem as Cognitive

------------------------------------------------------------------------
-- Exact finite empirical distributions.  Expectations are represented by
-- numerator/sample-count pairs so no hidden floating-point or division axiom
-- is introduced into the proof layer.
------------------------------------------------------------------------

eqNat : Nat → Nat → Nat
eqNat zero zero = 1
eqNat zero (suc _) = 0
eqNat (suc _) zero = 0
eqNat (suc m) (suc n) = eqNat m n

countNat : Nat → List Nat → Nat
countNat value [] = 0
countNat value (x ∷ xs) = eqNat value x + countNat value xs

record FiniteNatDistribution : Set where
  constructor finiteNatDistribution
  field
    samples : List Nat
    sampleCount : Nat
    massAt : Nat → Nat
    totalDepthNumerator : Nat

sumNat : List Nat → Nat
sumNat [] = 0
sumNat (x ∷ xs) = x + sumNat xs

fromSamples : List Nat → FiniteNatDistribution
fromSamples xs =
  finiteNatDistribution xs (length xs) (λ n → countNat n xs) (sumNat xs)

stackDepths :
  ∀ {system} →
  List (Cognitive.Configuration system) →
  List Nat
stackDepths [] = []
stackDepths (config ∷ configs) =
  Cognitive.stackDepth config ∷ stackDepths configs

stackDepthDistribution :
  ∀ {system} →
  List (Cognitive.Configuration system) →
  FiniteNatDistribution
stackDepthDistribution configs = fromSamples (stackDepths configs)

------------------------------------------------------------------------
-- Baseline-margin distribution.  Positive, boundary, and negative masses are
-- kept separately; positive/negative magnitudes remain available as samples.
------------------------------------------------------------------------

positiveMagnitude : Cognitive.SignedMargin → Nat
positiveMagnitude (Cognitive.positiveMargin n) = n
positiveMagnitude _ = 0

negativeMagnitude : Cognitive.SignedMargin → Nat
negativeMagnitude (Cognitive.negativeMargin n) = n
negativeMagnitude _ = 0

positiveIndicator : Cognitive.SignedMargin → Nat
positiveIndicator (Cognitive.positiveMargin _) = 1
positiveIndicator _ = 0

boundaryIndicator : Cognitive.SignedMargin → Nat
boundaryIndicator Cognitive.boundaryMargin = 1
boundaryIndicator _ = 0

negativeIndicator : Cognitive.SignedMargin → Nat
negativeIndicator (Cognitive.negativeMargin _) = 1
negativeIndicator _ = 0

sumMarginMap :
  (Cognitive.SignedMargin → Nat) →
  List Cognitive.SignedMargin →
  Nat
sumMarginMap f [] = 0
sumMarginMap f (margin ∷ margins) = f margin + sumMarginMap f margins

record BaselineMarginDistribution : Set where
  constructor baselineMarginDistribution
  field
    marginSamples : List Cognitive.SignedMargin
    positiveMass : Nat
    boundaryMass : Nat
    negativeMass : Nat
    positiveMagnitudeSum : Nat
    negativeMagnitudeSum : Nat

baselineMarginDistribution :
  List Cognitive.SignedMargin → BaselineMarginDistribution
baselineMarginDistribution margins =
  baselineMarginDistribution
    margins
    (sumMarginMap positiveIndicator margins)
    (sumMarginMap boundaryIndicator margins)
    (sumMarginMap negativeIndicator margins)
    (sumMarginMap positiveMagnitude margins)
    (sumMarginMap negativeMagnitude margins)

canonicalMargins : List Cognitive.SignedMargin
canonicalMargins =
  Cognitive.positiveMargin 3
  ∷ Cognitive.boundaryMargin
  ∷ Cognitive.negativeMargin 2
  ∷ Cognitive.positiveMargin 1
  ∷ []

canonicalPositiveMassIsTwo :
  BaselineMarginDistribution.positiveMass
    (baselineMarginDistribution canonicalMargins)
  ≡ 2
canonicalPositiveMassIsTwo = refl

canonicalBoundaryMassIsOne :
  BaselineMarginDistribution.boundaryMass
    (baselineMarginDistribution canonicalMargins)
  ≡ 1
canonicalBoundaryMassIsOne = refl

canonicalNegativeMassIsOne :
  BaselineMarginDistribution.negativeMass
    (baselineMarginDistribution canonicalMargins)
  ≡ 1
canonicalNegativeMassIsOne = refl
