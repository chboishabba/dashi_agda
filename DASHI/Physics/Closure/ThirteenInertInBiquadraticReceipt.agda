module DASHI.Physics.Closure.ThirteenInertInBiquadraticReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CMCorrectionToT13Receipt as CM

------------------------------------------------------------------------
-- Splitting of 13 in Q(sqrt(-3),sqrt(-7)).
--
-- The quadratic characters are (+1,-1,-1) for the subfields
-- Q(sqrt(-3)), Q(sqrt(-7)), and Q(sqrt(21)).  Hence Frobenius has order 2
-- in the biquadratic Galois group.  The rational prime 13 does not stay as a
-- single degree-4 prime; it splits into two degree-2 primes in the degree-4
-- biquadratic CM field.

data BiquadraticSplittingType : Set where
  twoDegreeTwoPrimes :
    BiquadraticSplittingType

data ThirteenBiquadraticStatus : Set where
  thirteenSplittingInBiquadraticRecorded :
    ThirteenBiquadraticStatus

data ThirteenBiquadraticBlocker : Set where
  splittingTypeDoesNotComputeCMCorrection :
    ThirteenBiquadraticBlocker

  idealClassActionStillMissing :
    ThirteenBiquadraticBlocker

  physicalCKMInterpretationNotBound :
    ThirteenBiquadraticBlocker

canonicalThirteenBiquadraticBlockers :
  List ThirteenBiquadraticBlocker
canonicalThirteenBiquadraticBlockers =
  splittingTypeDoesNotComputeCMCorrection
  ∷ idealClassActionStillMissing
  ∷ physicalCKMInterpretationNotBound
  ∷ []

data ThirteenBiquadraticPromotion : Set where

thirteenBiquadraticPromotionImpossibleHere :
  ThirteenBiquadraticPromotion →
  ⊥
thirteenBiquadraticPromotionImpossibleHere ()

record ThirteenInertInBiquadraticReceipt : Setω where
  field
    status :
      ThirteenBiquadraticStatus

    cmCorrectionReceiptConsumed :
      Bool

    cmCorrectionReceiptConsumedIsTrue :
      cmCorrectionReceiptConsumed ≡ true

    minusThreeSplitWitness :
      CM.qsqrtMinusThreeStatus CM.canonicalCMCorrectionToT13Receipt
      ≡
      CM.split

    minusSevenInertWitness :
      CM.qsqrtMinusSevenStatus CM.canonicalCMCorrectionToT13Receipt
      ≡
      CM.inert

    prime :
      Nat

    primeIsThirteen :
      prime ≡ 13

    characterMinusThree :
      String

    characterMinusThreeIsPlusOne :
      characterMinusThree ≡ "(-3/13)=+1"

    characterMinusSeven :
      String

    characterMinusSevenIsMinusOne :
      characterMinusSeven ≡ "(-7/13)=-1"

    characterTwentyOne :
      String

    characterTwentyOneIsMinusOne :
      characterTwentyOne ≡ "(21/13)=-1"

    frobeniusOrder :
      Nat

    frobeniusOrderIsTwo :
      frobeniusOrder ≡ 2

    splittingType :
      BiquadraticSplittingType

    splittingTypeIsTwoDegreeTwoPrimes :
      splittingType ≡ twoDegreeTwoPrimes

    singleDegreeFourPrime :
      Bool

    singleDegreeFourPrimeIsFalse :
      singleDegreeFourPrime ≡ false

    twoDegreeTwoPrimeFactors :
      Bool

    twoDegreeTwoPrimeFactorsIsTrue :
      twoDegreeTwoPrimeFactors ≡ true

    cmCorrectionDerivedFromSplitting :
      Bool

    cmCorrectionDerivedFromSplittingIsFalse :
      cmCorrectionDerivedFromSplitting ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List ThirteenBiquadraticBlocker

    blockersAreCanonical :
      blockers ≡ canonicalThirteenBiquadraticBlockers

    promotionFlags :
      List ThirteenBiquadraticPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open ThirteenInertInBiquadraticReceipt public

canonicalThirteenInertInBiquadraticReceipt :
  ThirteenInertInBiquadraticReceipt
canonicalThirteenInertInBiquadraticReceipt =
  record
    { status =
        thirteenSplittingInBiquadraticRecorded
    ; cmCorrectionReceiptConsumed =
        true
    ; cmCorrectionReceiptConsumedIsTrue =
        refl
    ; minusThreeSplitWitness =
        refl
    ; minusSevenInertWitness =
        refl
    ; prime =
        13
    ; primeIsThirteen =
        refl
    ; characterMinusThree =
        "(-3/13)=+1"
    ; characterMinusThreeIsPlusOne =
        refl
    ; characterMinusSeven =
        "(-7/13)=-1"
    ; characterMinusSevenIsMinusOne =
        refl
    ; characterTwentyOne =
        "(21/13)=-1"
    ; characterTwentyOneIsMinusOne =
        refl
    ; frobeniusOrder =
        2
    ; frobeniusOrderIsTwo =
        refl
    ; splittingType =
        twoDegreeTwoPrimes
    ; splittingTypeIsTwoDegreeTwoPrimes =
        refl
    ; singleDegreeFourPrime =
        false
    ; singleDegreeFourPrimeIsFalse =
        refl
    ; twoDegreeTwoPrimeFactors =
        true
    ; twoDegreeTwoPrimeFactorsIsTrue =
        refl
    ; cmCorrectionDerivedFromSplitting =
        false
    ; cmCorrectionDerivedFromSplittingIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalThirteenBiquadraticBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The character triple (+1,-1,-1) gives Frobenius order 2 in the biquadratic Galois group"
        ∷ "Therefore 13 splits as two degree-2 primes, not one degree-4 prime"
        ∷ "This splitting fact alone does not compute the CM-specialised T13 correction"
        ∷ "No physical CKM promotion is asserted"
        ∷ []
    }

thirteenSplitsAsTwoDegreeTwoPrimes :
  twoDegreeTwoPrimeFactors canonicalThirteenInertInBiquadraticReceipt ≡ true
thirteenSplitsAsTwoDegreeTwoPrimes =
  refl

thirteenBiquadraticNoCKMPromotion :
  physicalCKMPromoted canonicalThirteenInertInBiquadraticReceipt ≡ false
thirteenBiquadraticNoCKMPromotion =
  refl
