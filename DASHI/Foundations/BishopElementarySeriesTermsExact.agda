module DASHI.Foundations.BishopElementarySeriesTermsExact where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Rational.Unnormalised using (ℚᵘ)

import Real as BishopReal
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Series
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Concrete coefficient formulas for sine, cosine, exponential and -log(1-x).
-- Bishop supplies real multiplication, natural powers and rational embedding.
-- Denominator construction is isolated in one factorial/positive-integer record.
------------------------------------------------------------------------

record BishopReciprocalCoefficientData : Set₁ where
  field
    inverseFactorial : Nat → ℚᵘ
    inversePositiveInteger : Nat → ℚᵘ

    inverseFactorialZeroExact : Set
    inverseFactorialSuccessorExact : ∀ n → Set
    inversePositiveIntegerDefinition : ∀ n → Set

    factorialDenominatorNonzero : ∀ n → Set
    positiveIntegerDenominatorNonzero : ∀ n → Set

open BishopReciprocalCoefficientData public

two : Nat
two = suc (suc zero)

oddExponent : Nat → Nat
oddExponent n = two * n + suc zero

evenExponent : Nat → Nat
evenExponent n = two * n

alternatingSign : Nat → Bishop.Bishopℝ
alternatingSign zero = Bishop.bishopOne
alternatingSign (suc n) = Bishop.bishopNeg (alternatingSign n)

embeddedInverseFactorial :
  BishopReciprocalCoefficientData → Nat → Bishop.Bishopℝ
embeddedInverseFactorial coefficients n =
  BishopReal._⋆ (inverseFactorial coefficients n)

embeddedInversePositiveInteger :
  BishopReciprocalCoefficientData → Nat → Bishop.Bishopℝ
embeddedInversePositiveInteger coefficients n =
  BishopReal._⋆ (inversePositiveInteger coefficients n)

sineTerm :
  BishopReciprocalCoefficientData →
  Bishop.Bishopℝ → Nat → Bishop.Bishopℝ
sineTerm coefficients point n =
  Bishop.bishopMul (alternatingSign n)
    (Bishop.bishopMul
      (BishopReal.pow point (oddExponent n))
      (embeddedInverseFactorial coefficients (oddExponent n)))

cosineTerm :
  BishopReciprocalCoefficientData →
  Bishop.Bishopℝ → Nat → Bishop.Bishopℝ
cosineTerm coefficients point n =
  Bishop.bishopMul (alternatingSign n)
    (Bishop.bishopMul
      (BishopReal.pow point (evenExponent n))
      (embeddedInverseFactorial coefficients (evenExponent n)))

exponentialTerm :
  BishopReciprocalCoefficientData →
  Bishop.Bishopℝ → Nat → Bishop.Bishopℝ
exponentialTerm coefficients point n =
  Bishop.bishopMul
    (BishopReal.pow point n)
    (embeddedInverseFactorial coefficients n)

negativeLogOneMinusTerm :
  BishopReciprocalCoefficientData →
  Bishop.Bishopℝ → Nat → Bishop.Bishopℝ
negativeLogOneMinusTerm coefficients point n =
  Bishop.bishopMul
    (BishopReal.pow point (suc n))
    (embeddedInversePositiveInteger coefficients (suc n))

record BishopElementarySeriesConvergenceProofs
    (coefficients : BishopReciprocalCoefficientData) : Set₁ where
  field
    sineAbsoluteConvergence : ∀ point →
      Bishop.BishopAbsoluteSeriesConvergent (sineTerm coefficients point)
    cosineAbsoluteConvergence : ∀ point →
      Bishop.BishopAbsoluteSeriesConvergent (cosineTerm coefficients point)
    exponentialAbsoluteConvergence : ∀ point →
      Bishop.BishopAbsoluteSeriesConvergent (exponentialTerm coefficients point)

    InOpenUnitInterval : Bishop.Bishopℝ → Set
    negativeLogAbsoluteConvergence : ∀ point →
      InOpenUnitInterval point →
      Bishop.BishopAbsoluteSeriesConvergent
        (negativeLogOneMinusTerm coefficients point)

    sineCoefficientRecurrenceExact : ∀ point index → Set
    cosineCoefficientRecurrenceExact : ∀ point index → Set
    exponentialCoefficientRecurrenceExact : ∀ point index → Set
    negativeLogCoefficientRecurrenceExact : ∀ point index → Set

    sineOddPowersAndFactorialsExact : ∀ point index → Set
    cosineEvenPowersAndFactorialsExact : ∀ point index → Set
    exponentialPowersAndFactorialsExact : ∀ point index → Set
    negativeLogPowersOverPositiveIntegersExact : ∀ point index → Set

    sineAlternatingSignsExact : ∀ point index → Set
    cosineAlternatingSignsExact : ∀ point index → Set

open BishopElementarySeriesConvergenceProofs public

asBishopElementaryPowerSeriesData :
  (coefficients : BishopReciprocalCoefficientData) →
  BishopElementarySeriesConvergenceProofs coefficients →
  Series.BishopElementaryPowerSeriesData
asBishopElementaryPowerSeriesData coefficients proofs = record
  { rational = BishopReal._⋆
  ; rationalDefinition = refl
  ; sineTerm = sineTerm coefficients
  ; cosineTerm = cosineTerm coefficients
  ; exponentialTerm = exponentialTerm coefficients
  ; negativeLogOneMinusTerm = negativeLogOneMinusTerm coefficients
  ; sineAbsoluteConvergence = sineAbsoluteConvergence proofs
  ; cosineAbsoluteConvergence = cosineAbsoluteConvergence proofs
  ; exponentialAbsoluteConvergence = exponentialAbsoluteConvergence proofs
  ; InOpenUnitInterval = InOpenUnitInterval proofs
  ; negativeLogAbsoluteConvergence = negativeLogAbsoluteConvergence proofs
  ; sineCoefficientRecurrenceExact = sineCoefficientRecurrenceExact proofs
  ; cosineCoefficientRecurrenceExact = cosineCoefficientRecurrenceExact proofs
  ; exponentialCoefficientRecurrenceExact = exponentialCoefficientRecurrenceExact proofs
  ; negativeLogCoefficientRecurrenceExact = negativeLogCoefficientRecurrenceExact proofs
  ; sineOddPowersAndFactorialsExact = sineOddPowersAndFactorialsExact proofs
  ; cosineEvenPowersAndFactorialsExact = cosineEvenPowersAndFactorialsExact proofs
  ; exponentialPowersAndFactorialsExact = exponentialPowersAndFactorialsExact proofs
  ; negativeLogPowersOverPositiveIntegersExact =
      negativeLogPowersOverPositiveIntegersExact proofs
  ; sineAlternatingSignsExact = sineAlternatingSignsExact proofs
  ; cosineAlternatingSignsExact = cosineAlternatingSignsExact proofs
  }

bishopElementaryTermDefinitionLevel : ProofLevel
bishopElementaryTermDefinitionLevel = machineChecked

bishopReciprocalCoefficientInputsLevel : ProofLevel
bishopReciprocalCoefficientInputsLevel = conditional

bishopElementarySeriesConvergenceInputsLevel : ProofLevel
bishopElementarySeriesConvergenceInputsLevel = conditional
