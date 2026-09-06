module DASHI.Core.FiniteUniformProbabilityNormalizationExact where

------------------------------------------------------------------------
-- FINITE UNIFORM PROBABILITY NORMALIZATION
--
-- A uniform finite branching process can be normalized without introducing
-- division into the kernel-visible proof.  Store probabilities as exact finite
-- fractions.  When two fractions have the same denominator, a numerator bound
-- is exactly the finite probability comparison needed by the stopping tail.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Nat using (_≤_)

import DASHI.Core.FiniteBlockSurvivalCountDecayExact as CountDecay

record FiniteFraction : Set where
  constructor finiteFraction
  field
    numerator : Nat
    denominator : Nat

open FiniteFraction public

record SameDenominatorLe
    (left right : FiniteFraction) : Set where
  constructor sameDenominatorLe
  field
    denominatorsEqual : denominator left ≡ denominator right
    numeratorsOrdered : numerator left ≤ numerator right

open SameDenominatorLe public

survivalDenominator :
  CountDecay.BlockSurvivalRecurrence → Nat → Nat
survivalDenominator data q =
  CountDecay.powNat (CountDecay.branchFactor data) q
  * CountDecay.survivors data 0

survivalFraction :
  CountDecay.BlockSurvivalRecurrence → Nat → FiniteFraction
survivalFraction data q =
  finiteFraction
    (CountDecay.survivors data q)
    (survivalDenominator data q)

envelopeFraction :
  CountDecay.BlockSurvivalRecurrence → Nat → FiniteFraction
envelopeFraction data q =
  finiteFraction
    (CountDecay.powNat (CountDecay.contractionCount data) q
      * CountDecay.survivors data 0)
    (survivalDenominator data q)

survivalFractionBelowEnvelope :
  (data : CountDecay.BlockSurvivalRecurrence) →
  (q : Nat) →
  SameDenominatorLe
    (survivalFraction data q)
    (envelopeFraction data q)
survivalFractionBelowEnvelope data q =
  sameDenominatorLe refl
    (CountDecay.survivorCountGeometricBound data q)

------------------------------------------------------------------------
-- For a binary hitting block of length m:
--
--   B = 2^m,
--   c = B - 1.
--
-- The exact finite fraction therefore represents the envelope
--
--   ((B-1)/B)^q
--
-- up to the common initial survivor count.  Promotion to a rational or real
-- quotient is a scalar-backend interpretation, not additional combinatorics.
------------------------------------------------------------------------

record ProbabilityNormalizationBoundary : Set where
  constructor probabilityNormalizationBoundary
  field
    exactCommonDenominatorFractionOwned : Bool
    geometricFractionComparisonOwned : Bool
    rationalScalarDivisionRequiredForFiniteTail : Bool
    realScalarDivisionRequiredForFiniteTail : Bool
    scalarBackendInterpretationOptional : Bool

canonicalProbabilityNormalizationBoundary :
  ProbabilityNormalizationBoundary
canonicalProbabilityNormalizationBoundary =
  probabilityNormalizationBoundary true true false false true

finiteNormalizationOwned :
  ProbabilityNormalizationBoundary.exactCommonDenominatorFractionOwned
    canonicalProbabilityNormalizationBoundary
  ≡ true
finiteNormalizationOwned = refl

realDivisionNotRequiredForFiniteTail :
  ProbabilityNormalizationBoundary.realScalarDivisionRequiredForFiniteTail
    canonicalProbabilityNormalizationBoundary
  ≡ false
realDivisionNotRequiredForFiniteTail = refl
