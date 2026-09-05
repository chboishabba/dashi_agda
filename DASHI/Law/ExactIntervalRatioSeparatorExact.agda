module DASHI.Law.ExactIntervalRatioSeparatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.PartialIdentificationMissingnessBoundsExact as Bounds

------------------------------------------------------------------------
-- Exact arithmetic separator for partially identified rates.
--
-- For A > B robustly, compare the smallest admissible A rate with the
-- largest admissible B rate:
--
--   aL / dAU > bU / dBL
--
-- using only natural-number cross multiplication:
--
--   aL * dBL > bU * dAU.
--
-- Denominator positivity and interval ordering are checked before the
-- separator is allowed to classify a direction.
------------------------------------------------------------------------

natLT : ℕ → ℕ → Bool
natLT zero zero = false
natLT zero (suc n) = true
natLT (suc m) zero = false
natLT (suc m) (suc n) = natLT m n

natLE : ℕ → ℕ → Bool
natLE zero n = true
natLE (suc m) zero = false
natLE (suc m) (suc n) = natLE m n

positive : ℕ → Bool
positive zero = false
positive (suc n) = true

andB : Bool → Bool → Bool
andB true b = b
andB false b = false

ratioBoundsWellFormed : Bounds.RatioBounds → Bool
ratioBoundsWellFormed r =
  andB
    (natLE (Bounds.numeratorLower r) (Bounds.numeratorUpper r))
    (andB
      (natLE (Bounds.denominatorLower r) (Bounds.denominatorUpper r))
      (positive (Bounds.denominatorLower r)))

pairBoundsWellFormed : Bounds.RatioBounds → Bounds.RatioBounds → Bool
pairBoundsWellFormed a b = andB (ratioBoundsWellFormed a) (ratioBoundsWellFormed b)

-- Worst-case products for A > B.
positiveLeftProduct : Bounds.RatioBounds → Bounds.RatioBounds → ℕ
positiveLeftProduct a b = Bounds.numeratorLower a * Bounds.denominatorLower b

positiveRightProduct : Bounds.RatioBounds → Bounds.RatioBounds → ℕ
positiveRightProduct a b = Bounds.numeratorUpper b * Bounds.denominatorUpper a

-- Worst-case products for A < B.
negativeLeftProduct : Bounds.RatioBounds → Bounds.RatioBounds → ℕ
negativeLeftProduct a b = Bounds.numeratorUpper a * Bounds.denominatorUpper b

negativeRightProduct : Bounds.RatioBounds → Bounds.RatioBounds → ℕ
negativeRightProduct a b = Bounds.numeratorLower b * Bounds.denominatorLower a

robustPositiveSeparated : Bounds.RatioBounds → Bounds.RatioBounds → Bool
robustPositiveSeparated a b =
  andB
    (pairBoundsWellFormed a b)
    (natLT (positiveRightProduct a b) (positiveLeftProduct a b))

robustNegativeSeparated : Bounds.RatioBounds → Bounds.RatioBounds → Bool
robustNegativeSeparated a b =
  andB
    (pairBoundsWellFormed a b)
    (natLT (negativeLeftProduct a b) (negativeRightProduct a b))

data ArithmeticIdentification : Set where
  arithmeticRobustPositive arithmeticRobustNegative arithmeticUnidentified malformedBounds : ArithmeticIdentification

classifyRatioBounds : Bounds.RatioBounds → Bounds.RatioBounds → ArithmeticIdentification
classifyRatioBounds a b with pairBoundsWellFormed a b
... | false = malformedBounds
... | true with natLT (positiveRightProduct a b) (positiveLeftProduct a b)
...   | true = arithmeticRobustPositive
...   | false with natLT (negativeLeftProduct a b) (negativeRightProduct a b)
...     | true = arithmeticRobustNegative
...     | false = arithmeticUnidentified

------------------------------------------------------------------------
-- Derived receipt contains arithmetic data, not a trusted ordering flag.
------------------------------------------------------------------------

record ArithmeticSeparationReceipt (a b : Bounds.RatioBounds) : Set where
  constructor arithmeticSeparationReceipt
  field
    classification : ArithmeticIdentification
    positiveWorstCaseLeft : ℕ
    positiveWorstCaseRight : ℕ
    negativeWorstCaseLeft : ℕ
    negativeWorstCaseRight : ℕ
    separatorReference : String

open ArithmeticSeparationReceipt public

deriveSeparationReceipt :
  (a b : Bounds.RatioBounds) → ArithmeticSeparationReceipt a b
deriveSeparationReceipt a b = arithmeticSeparationReceipt
  (classifyRatioBounds a b)
  (positiveLeftProduct a b)
  (positiveRightProduct a b)
  (negativeLeftProduct a b)
  (negativeRightProduct a b)
  "exact natural-number cross multiplication; no floating-point division"

------------------------------------------------------------------------
-- Canonical robust-positive and overlapping regressions.
------------------------------------------------------------------------

canonicalA : Bounds.RatioBounds
canonicalA = Bounds.ratioBounds 12 18 40 53
  "group A partially identified selection rate"
  "synthetic arithmetic regression"

canonicalSeparatedB : Bounds.RatioBounds
canonicalSeparatedB = Bounds.ratioBounds 4 5 40 45
  "group B rate lies strictly below group A under worst-case allocation"
  "synthetic arithmetic regression"

canonicalOverlapB : Bounds.RatioBounds
canonicalOverlapB = Bounds.ratioBounds 10 20 40 50
  "group B interval overlaps group A interval"
  "synthetic arithmetic regression"

canonicalPositiveLeft : positiveLeftProduct canonicalA canonicalSeparatedB ≡ 480
canonicalPositiveLeft = refl

canonicalPositiveRight : positiveRightProduct canonicalA canonicalSeparatedB ≡ 265
canonicalPositiveRight = refl

canonicalPositiveSeparation :
  classifyRatioBounds canonicalA canonicalSeparatedB ≡ arithmeticRobustPositive
canonicalPositiveSeparation = refl

canonicalOverlapUnidentified :
  classifyRatioBounds canonicalA canonicalOverlapB ≡ arithmeticUnidentified
canonicalOverlapUnidentified = refl

zeroDenominatorBounds : Bounds.RatioBounds
zeroDenominatorBounds = Bounds.ratioBounds 1 2 0 4
  "invalid denominator interval"
  "synthetic malformed regression"

zeroDenominatorRejected :
  classifyRatioBounds zeroDenominatorBounds canonicalSeparatedB ≡ malformedBounds
zeroDenominatorRejected = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record ExactSeparatorBoundary : Set where
  constructor exactSeparatorBoundary
  field
    floatingPointRequired : Bool
    floatingPointRequiredIsFalse : floatingPointRequired ≡ false
    overlappingIntervalsMayPromoteRobustDirection : Bool
    overlappingIntervalsMayPromoteRobustDirectionIsFalse :
      overlappingIntervalsMayPromoteRobustDirection ≡ false
    zeroDenominatorMayBeCrossMultiplied : Bool
    zeroDenominatorMayBeCrossMultipliedIsFalse :
      zeroDenominatorMayBeCrossMultiplied ≡ false
    derivedDirectionEqualsExactMagnitude : Bool
    derivedDirectionEqualsExactMagnitudeIsFalse :
      derivedDirectionEqualsExactMagnitude ≡ false

canonicalExactSeparatorBoundary : ExactSeparatorBoundary
canonicalExactSeparatorBoundary = exactSeparatorBoundary false refl false refl false refl false refl
