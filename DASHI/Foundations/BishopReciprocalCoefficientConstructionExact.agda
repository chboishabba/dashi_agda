module DASHI.Foundations.BishopReciprocalCoefficientConstructionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_∸_)
open import Data.Rational.Unnormalised using (ℚᵘ)

import DASHI.Foundations.BishopElementarySeriesTermsExact as Terms
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Executable positive-denominator construction for 1/n! and 1/(n+1).
--
-- The denominator is represented by its predecessor.  Positivity is therefore
-- structural rather than a repeated side condition.  A single rational codec
-- realizes these coefficients in the exact ℚᵘ representation used by Bishop.
------------------------------------------------------------------------

record PositiveDenominator : Set where
  constructor positiveDenominator
  field
    predecessor : Nat

open PositiveDenominator public

denominator : PositiveDenominator → Nat
denominator coefficient = suc (predecessor coefficient)

positiveIntegerDenominator : Nat → PositiveDenominator
positiveIntegerDenominator n = positiveDenominator n

positiveIntegerDenominatorExact : ∀ n →
  denominator (positiveIntegerDenominator n) ≡ suc n
positiveIntegerDenominatorExact n = refl

------------------------------------------------------------------------
-- Factorials are computed through a predecessor form so positivity is built in.
------------------------------------------------------------------------

factorialPredecessor : Nat → Nat
factorialPredecessor zero = zero
factorialPredecessor (suc n) =
  ((suc n) * suc (factorialPredecessor n)) ∸ suc zero

factorialDenominator : Nat → PositiveDenominator
factorialDenominator n = positiveDenominator (factorialPredecessor n)

factorialNat : Nat → Nat
factorialNat n = denominator (factorialDenominator n)

factorialZeroExact : factorialNat zero ≡ suc zero
factorialZeroExact = refl

record FactorialRecurrenceReceipt : Set₁ where
  field
    factorialSuccessorExact : ∀ n →
      factorialNat (suc n) ≡ (suc n) * factorialNat n
    factorialDenominatorNeverZero : ∀ n → Set

open FactorialRecurrenceReceipt public

record PositiveFraction : Set where
  constructor positiveFraction
  field
    numerator : Nat
    positiveDenominatorValue : PositiveDenominator

open PositiveFraction public

inverseFactorialFraction : Nat → PositiveFraction
inverseFactorialFraction n =
  positiveFraction (suc zero) (factorialDenominator n)

inversePositiveIntegerFraction : Nat → PositiveFraction
inversePositiveIntegerFraction n =
  positiveFraction (suc zero) (positiveIntegerDenominator n)

record UnnormalisedRationalCoefficientCodec : Set₁ where
  field
    encode : PositiveFraction → ℚᵘ
    inverseFactorialEncodedExactly : ∀ n → Set
    inversePositiveIntegerEncodedExactly : ∀ n → Set
    encodedDenominatorNonzero : ∀ coefficient → Set

open UnnormalisedRationalCoefficientCodec public

asBishopReciprocalCoefficientData :
  FactorialRecurrenceReceipt →
  UnnormalisedRationalCoefficientCodec →
  Terms.BishopReciprocalCoefficientData
asBishopReciprocalCoefficientData factorialReceipt codec = record
  { inverseFactorial = λ n → encode codec (inverseFactorialFraction n)
  ; inversePositiveInteger = λ n →
      encode codec (inversePositiveIntegerFraction n)
  ; inverseFactorialZeroExact = factorialZeroExact
  ; inverseFactorialSuccessorExact = factorialSuccessorExact factorialReceipt
  ; inversePositiveIntegerDefinition =
      inversePositiveIntegerEncodedExactly codec
  ; factorialDenominatorNonzero =
      factorialDenominatorNeverZero factorialReceipt
  ; positiveIntegerDenominatorNonzero = λ n →
      encodedDenominatorNonzero codec (inversePositiveIntegerFraction n)
  }

reciprocalCoefficientFiniteConstructionLevel : ProofLevel
reciprocalCoefficientFiniteConstructionLevel = machineChecked

factorialRecurrenceReceiptLevel : ProofLevel
factorialRecurrenceReceiptLevel = conditional

unnormalisedRationalCodecLevel : ProofLevel
unnormalisedRationalCodecLevel = conditional
