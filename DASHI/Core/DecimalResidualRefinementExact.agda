module DASHI.Core.DecimalResidualRefinementExact where

------------------------------------------------------------------------
-- SOURCE / PROVENANCE
--
-- The concrete decimal recursion formalised here comes from the supplied
-- DASHI discussion notes (2026-08-26): repeated refinement of a coarse digit N
-- by appending the same decimal digit, e.g. 9 -> 9.9 -> 9.99 -> ... .
--
-- The fixed-point / contraction interpretation belongs to the standard
-- contraction-mapping literature.  The present module does NOT reconstruct a
-- real-analysis limit; it proves only the finite radix arithmetic and the
-- exact complement identity used by the discussion.
--
-- Stefan Banach,
-- "Sur les operations dans les ensembles abstraits et leur application aux
-- equations integrales", Fundamenta Mathematicae 3 (1922), 133--181.
-- Historical source for the contraction principle; no DOI is asserted here.
--
-- DASHI CONTRIBUTION
--
-- Keep three claims separate:
--   * finite repeated-digit refinement;
--   * complement arithmetic over the ten decimal digits;
--   * any analytic statement about the infinite real limit.
-- Only the first two are proved in this finite module.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

pow : Nat → Nat → Nat
pow base zero = 1
pow base (suc exponent) = base * pow base exponent

data DecimalDigit : Set where
  d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : DecimalDigit

digitValue : DecimalDigit → Nat
digitValue d0 = 0
digitValue d1 = 1
digitValue d2 = 2
digitValue d3 = 3
digitValue d4 = 4
digitValue d5 = 5
digitValue d6 = 6
digitValue d7 = 7
digitValue d8 = 8
digitValue d9 = 9

digitComplement : DecimalDigit → Nat
digitComplement d0 = 9
digitComplement d1 = 8
digitComplement d2 = 7
digitComplement d3 = 6
digitComplement d4 = 5
digitComplement d5 = 4
digitComplement d6 = 3
digitComplement d7 = 2
digitComplement d8 = 1
digitComplement d9 = 0

digitPlusComplementIsNine :
  (digit : DecimalDigit) →
  digitValue digit + digitComplement digit ≡ 9
digitPlusComplementIsNine d0 = refl
digitPlusComplementIsNine d1 = refl
digitPlusComplementIsNine d2 = refl
digitPlusComplementIsNine d3 = refl
digitPlusComplementIsNine d4 = refl
digitPlusComplementIsNine d5 = refl
digitPlusComplementIsNine d6 = refl
digitPlusComplementIsNine d7 = refl
digitPlusComplementIsNine d8 = refl
digitPlusComplementIsNine d9 = refl

------------------------------------------------------------------------
-- Finite repeated-digit decimal refinement.
--
-- `decimalRefinementNumerator digit depth / 10^depth` is the finite decimal
-- with `depth` repeated fractional copies of `digit`:
--
--   depth 0 : N
--   depth 1 : N.N
--   depth 2 : N.NN
--
-- The representation is exact and uses only Nat arithmetic.
------------------------------------------------------------------------

decimalRefinementNumerator : DecimalDigit → Nat → Nat
decimalRefinementNumerator digit zero = digitValue digit
decimalRefinementNumerator digit (suc depth) =
  10 * decimalRefinementNumerator digit depth + digitValue digit

decimalRefinementDenominator : Nat → Nat
decimalRefinementDenominator depth = pow 10 depth

decimalRefinementStep :
  (digit : DecimalDigit) →
  (depth : Nat) →
  decimalRefinementNumerator digit (suc depth)
  ≡ 10 * decimalRefinementNumerator digit depth + digitValue digit
decimalRefinementStep digit depth = refl

nineDepthZero : decimalRefinementNumerator d9 0 ≡ 9
nineDepthZero = refl

nineDepthOne : decimalRefinementNumerator d9 1 ≡ 99
nineDepthOne = refl

nineDepthTwo : decimalRefinementNumerator d9 2 ≡ 999
nineDepthTwo = refl

nineDepthThree : decimalRefinementNumerator d9 3 ≡ 9999
nineDepthThree = refl

fiveDepthOne : decimalRefinementNumerator d5 1 ≡ 55
fiveDepthOne = refl

fiveDepthTwo : decimalRefinementNumerator d5 2 ≡ 555
fiveDepthTwo = refl

------------------------------------------------------------------------
-- Exact complement form of the discussion's limiting arithmetic.
--
-- Written over denominator 9, the claimed completed value has numerator 10N.
-- The next integer has numerator 9(N+1).  Their numerator gap is exactly the
-- decimal complement 9-N.  This is finite integer arithmetic; it is NOT a
-- proof here that the infinite decimal sequence converges in the reals.
------------------------------------------------------------------------

completedRefinementNumeratorOverNine : DecimalDigit → Nat
completedRefinementNumeratorOverNine digit = 10 * digitValue digit

nextIntegerNumeratorOverNine : DecimalDigit → Nat
nextIntegerNumeratorOverNine digit = 9 * (digitValue digit + 1)

completedGapNumeratorOverNine : DecimalDigit → Nat
completedGapNumeratorOverNine = digitComplement

nextIntegerSplitsAsCompletedPlusGap :
  (digit : DecimalDigit) →
  nextIntegerNumeratorOverNine digit
  ≡ completedRefinementNumeratorOverNine digit
      + completedGapNumeratorOverNine digit
nextIntegerSplitsAsCompletedPlusGap d0 = refl
nextIntegerSplitsAsCompletedPlusGap d1 = refl
nextIntegerSplitsAsCompletedPlusGap d2 = refl
nextIntegerSplitsAsCompletedPlusGap d3 = refl
nextIntegerSplitsAsCompletedPlusGap d4 = refl
nextIntegerSplitsAsCompletedPlusGap d5 = refl
nextIntegerSplitsAsCompletedPlusGap d6 = refl
nextIntegerSplitsAsCompletedPlusGap d7 = refl
nextIntegerSplitsAsCompletedPlusGap d8 = refl
nextIntegerSplitsAsCompletedPlusGap d9 = refl

nineCompletedGapIsZero : completedGapNumeratorOverNine d9 ≡ 0
nineCompletedGapIsZero = refl

zeroCompletedGapIsNine : completedGapNumeratorOverNine d0 ≡ 9
zeroCompletedGapIsNine = refl
