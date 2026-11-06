module DASHI.Mathematics.Complexity.Karp21N21BitWeightedComparisonEnvelopeExact where

------------------------------------------------------------------------
-- K05/N21: LENGTH-WEIGHTED BIT-COMPARISON BUDGET FOR ORIGINAL WORDS.
--
-- This is NOT a bit-tape step-count theorem for the existing Agda
-- Nat/Integer operations. The previous source owners supply:
--   allWordCombinedComparisonCount w <= 7 * (1 + |w|)^2
-- including malformed words. This owner charges each primitive
-- comparator an explicit conservative schedule of 1+|w| bit steps.
--
-- Therefore the *weighted schedule* fits a native degree-three
-- PolynomialBound. To promote to an actual machine clock one must
-- show that the selected bit-native comparator realises this
-- schedule on EVERY original operand. The gamma reader, signed
-- score accumulation and tape overhead are independently unpaid.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21FinFreeOriginalGraphComparisonEnvelopeExact as Count
import DASHI.Mathematics.Complexity.PolynomialBoundClosureExact as Poly
import DASHI.Core.EfficientRecoverableQuotientExact as ERQ

bitLengthCharge : Word.BitWord → Nat
bitLengthCharge word = suc (Word.encodingSize word)

lengthWeightedComparatorSchedule : Word.BitWord → Nat
lengthWeightedComparatorSchedule word =
  Count.allWordCombinedComparisonCount word * bitLengthCharge word

lengthWeightedComparisonAtMostCubicSchedule :
  (word : Word.BitWord) →
  lengthWeightedComparatorSchedule word ≤
    Count.combinedComparisonPolynomial (Word.encodingSize word)
      * bitLengthCharge word
lengthWeightedComparisonAtMostCubicSchedule word =
  NatP.*-mono-≤
    (Count.allWordCombinedComparisonBound word)
    NatP.≤-refl

onePlusLengthPolynomial : ERQ.PolynomialBound suc
onePlusLengthPolynomial =
  ERQ.polynomialBound 1 1 (λ _ → NatP.≤-refl)

weightedComparatorPolynomial : ERQ.PolynomialBound
  (λ n → Count.combinedComparisonPolynomial n * suc n)
weightedComparatorPolynomial =
  Poly.productPolynomialBound
    Count.combinedComparisonPolynomialBound
    onePlusLengthPolynomial

lengthWeightedComparatorPolynomialClock :
  (word : Word.BitWord) →
  lengthWeightedComparatorSchedule word ≤
    ERQ.coefficient weightedComparatorPolynomial
      * ERQ.pow (suc (Word.encodingSize word))
          (ERQ.exponent weightedComparatorPolynomial)
lengthWeightedComparatorPolynomialClock word =
  NatP.≤-trans
    (lengthWeightedComparisonAtMostCubicSchedule word)
    (ERQ.bounded weightedComparatorPolynomial
      (Word.encodingSize word))

-- An ACTUAL clock only follows after the original binary-native
-- comparator is shown pointwise to fit the per-operation charge.
-- The implementation-cost antecedent is proof relevant and cannot be
-- inferred from a Boolean status flag or the numerical count itself.
record OriginalN21ComparisonImplementationClock
  (word : Word.BitWord) : Set where
  field
    machineSteps : Nat
    implementationWithinLengthSchedule :
      machineSteps ≤ lengthWeightedComparatorSchedule word

originalN21ComparatorStepsPolynomial :
  (word : Word.BitWord) →
  OriginalN21ComparisonImplementationClock word →
  Nat
originalN21ComparatorStepsPolynomial word actual =
  OriginalN21ComparisonImplementationClock.machineSteps actual

originalN21ComparisonClockBound :
  (word : Word.BitWord) →
  (actual : OriginalN21ComparisonImplementationClock word) →
  OriginalN21ComparisonImplementationClock.machineSteps actual ≤
    ERQ.coefficient weightedComparatorPolynomial
      * ERQ.pow (suc (Word.encodingSize word))
          (ERQ.exponent weightedComparatorPolynomial)
originalN21ComparisonClockBound word actual =
  NatP.≤-trans
    (OriginalN21ComparisonImplementationClock.implementationWithinLengthSchedule actual)
    (lengthWeightedComparatorPolynomialClock word)
