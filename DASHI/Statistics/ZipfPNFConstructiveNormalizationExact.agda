module DASHI.Statistics.ZipfPNFConstructiveNormalizationExact where

-- 28 October 2026. Constructive positive rational normalization of the
-- finite shifted integer-exponent Zipf family into the existing PNF atoms.
-- Original rational algebra belongs to the Agda standard library.
-- Original Zipf/Estoup, Mandelbrot and Hurwitz mathematical priority stays
-- separate from this Johl Brown-directed, ChatGPT-assisted source adapter.
--
-- SOURCE-WRITTEN. No Agda compiler receipt is claimed from this module.
-- This is not a theorem of an empirical corpus, analytic continuation,
-- NS regularity, RH or an Ibrahim Monster 3B same-object representation.
--
-- Counts are positive (suc n). No fabricated normalization premise is passed
-- by callers. The source Fraction-to-ℚ accumulator equality is distinct.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base as Nat using (NonZero; nonZero)
open import Data.Rational.Base as R
  using (ℚ; 0ℚ; 1ℚ; Positive; NonNegative; normalize;
         nonNegative; _+_; _*_; 1/_)
import Data.Rational.Properties as ℚP

import DASHI.Statistics.ZipfFamilyFiniteExact as Zipf
import DASHI.Statistics.ZipfIIDTwoDrawAndPNFExact as Adapter
import DASHI.Cognition.PNF.GenericExpectedFibreRateExact as Expected
import DASHI.Core.FiniteUniformProbabilityNormalizationExact as Fraction

-- A rank r is zero-based, corresponding to physical rank r+1.
-- The denominator is exactly the existing family-owned positive power.

rawTerm : Nat → Nat → Nat → ℚ
rawTerm r shift exponent =
  R.normalize (suc zero) (Zipf.mandelbrotDenominator r shift exponent)
    {{Zipf.mandelbrotDenominatorNonZero r shift exponent}}

rawTermPositive : ∀ r shift exponent → R.Positive (rawTerm r shift exponent)
rawTermPositive r shift exponent =
  ℚP.normalize-pos (suc zero)
    (Zipf.mandelbrotDenominator r shift exponent)
    {{Zipf.mandelbrotDenominatorNonZero r shift exponent}}
    {{Nat.nonZero}}

-- This equality is definitional: the exact numerator/denominator matches
-- the source FiniteFraction *term*. A separate lemma must identify finite
-- repeated fraction addition with the rational sum.

rawTermMatchesSource :
  ∀ r shift exponent →
    rawTerm r shift exponent ≡
      R.normalize
        (Fraction.numerator (Zipf.finiteMandelbrotTerm r shift exponent))
        (Fraction.denominator (Zipf.finiteMandelbrotTerm r shift exponent))
        {{Zipf.mandelbrotDenominatorNonZero r shift exponent}}
rawTermMatchesSource r shift exponent = refl

rawSum : Nat → Nat → Nat → ℚ
rawSum zero shift exponent = 0ℚ
rawSum (suc n) shift exponent =
  rawTerm n shift exponent + rawSum n shift exponent

rawSumNonnegative : ∀ n shift exponent →
  R.NonNegative (rawSum n shift exponent)
rawSumNonnegative zero shift exponent =
  R.nonNegative ℚP.≤-refl
rawSumNonnegative (suc n) shift exponent =
  ℚP.nonNeg+nonNeg⇒nonNeg
    (rawTerm n shift exponent) (rawSum n shift exponent)
    {{ℚP.pos⇒nonNeg (rawTerm n shift exponent)
        {{rawTermPositive n shift exponent}}}}
    {{rawSumNonnegative n shift exponent}}

rawSumPositive : ∀ n shift exponent →
  R.Positive (rawSum (suc n) shift exponent)
rawSumPositive n shift exponent =
  ℚP.pos+nonNeg⇒pos
    (rawTerm n shift exponent) (rawSum n shift exponent)
    {{rawTermPositive n shift exponent}}
    {{rawSumNonnegative n shift exponent}}

-- A proof of strict positivity constructs the actual reciprocal.
-- The implicit NonZero witness is derived, never passed as a Bool.

inverseNormalizer : Nat → Nat → Nat → ℚ
inverseNormalizer n shift exponent =
  R.1/ (rawSum (suc n) shift exponent)
    {{ℚP.pos⇒nonZero (rawSum (suc n) shift exponent)
        {{rawSumPositive n shift exponent}}}}

inverseNormalizerPositive : ∀ n shift exponent →
  R.Positive (inverseNormalizer n shift exponent)
inverseNormalizerPositive n shift exponent =
  ℚP.1/pos⇒pos (rawSum (suc n) shift exponent)
    {{rawSumPositive n shift exponent}}

scaledSum : (count shift exponent : Nat) → ℚ → ℚ
scaledSum zero shift exponent factor = 0ℚ
scaledSum (suc n) shift exponent factor =
  rawTerm n shift exponent * factor +
  scaledSum n shift exponent factor

-- Distribution of the *same scalar factor* over the finite sum.
scaledSumFactors : ∀ count shift exponent factor →
  scaledSum count shift exponent factor ≡
    rawSum count shift exponent * factor
scaledSumFactors zero shift exponent factor =
  sym (ℚP.*-zeroˡ factor)
scaledSumFactors (suc n) shift exponent factor =
  trans
    (cong (rawTerm n shift exponent * factor +_)
      (scaledSumFactors n shift exponent factor))
    (sym
      (ℚP.*-distribʳ-+
        factor (rawTerm n shift exponent) (rawSum n shift exponent)))

-- Build exact PNF atoms rather than a duplicate probability carrier.
-- The factor is proved positive. The original rank term is also positive.

atomsWithFactor :
  (count shift exponent : Nat) (factor : ℚ) →
  R.Positive factor → List Expected.ProbabilityAtom
atomsWithFactor zero shift exponent factor positiveFactor = []
atomsWithFactor (suc n) shift exponent factor positiveFactor =
  Expected.probabilityAtom
    (rawTerm n shift exponent * factor)
    (ℚP.nonNegative⁻¹ (rawTerm n shift exponent * factor)
      {{ℚP.pos⇒nonNeg (rawTerm n shift exponent * factor)
        {{ℚP.pos*pos⇒pos
            (rawTerm n shift exponent) factor
            {{rawTermPositive n shift exponent}} {{positiveFactor}}}}}})
  ∷ atomsWithFactor n shift exponent factor positiveFactor

atomsTotalEqualsScaledSum :
  ∀ count shift exponent factor positiveFactor →
    Expected.probabilityTotal
      (atomsWithFactor count shift exponent factor positiveFactor)
    ≡ scaledSum count shift exponent factor
atomsTotalEqualsScaledSum zero shift exponent factor positiveFactor = refl
atomsTotalEqualsScaledSum (suc n) shift exponent factor positiveFactor =
  cong (rawTerm n shift exponent * factor +_)
    (atomsTotalEqualsScaledSum n shift exponent factor positiveFactor)

zipfPNFAtoms : (n shift exponent : Nat) → List Expected.ProbabilityAtom
zipfPNFAtoms n shift exponent =
  atomsWithFactor (suc n) shift exponent
    (inverseNormalizer n shift exponent)
    (inverseNormalizerPositive n shift exponent)

-- F13: the already-owned PNF total is *proved* to be one, not supplied
-- as an unverified Boolean or a manually entered list of mass values.
zipfPNFAtomsNormalize : ∀ n shift exponent →
  Expected.probabilityTotal (zipfPNFAtoms n shift exponent) ≡ 1ℚ
zipfPNFAtomsNormalize n shift exponent =
  trans
    (atomsTotalEqualsScaledSum (suc n) shift exponent
      (inverseNormalizer n shift exponent)
      (inverseNormalizerPositive n shift exponent))
    (trans
      (scaledSumFactors (suc n) shift exponent
        (inverseNormalizer n shift exponent))
      (ℚP.*-inverseʳ (rawSum (suc n) shift exponent)
        {{ℚP.pos⇒nonZero (rawSum (suc n) shift exponent)
          {{rawSumPositive n shift exponent}}}}))

-- Use the existing adapter's exact probability atoms and normalization.
-- IMPORTANT: false marks the *still unpaid* statement identifying this
-- ℚ sum with interpretation of Zipf.finiteHurwitz's FiniteFraction fold.
-- PNF normalization itself is independent of that accounting identity.
finiteZipfPNFAdapter : (n shift exponent : Nat) →
  Adapter.FiniteRankProbabilityAdapter
finiteZipfPNFAdapter n shift exponent =
  Adapter.finite-rank-probability-adapter
    (suc n) shift exponent
    (zipfPNFAtoms n shift exponent)
    (zipfPNFAtomsNormalize n shift exponent)
    "finite positive shifted rank weights"
    "Zipf/Estoup–Mandelbrot; Hurwitz; existing canonical PNF"
    false

zipfPNFConstantExpectation :
  (n shift exponent : Nat) (rate : ℚ) →
  Expected.constantRateExpectation rate (zipfPNFAtoms n shift exponent)
  ≡ rate
zipfPNFConstantExpectation n shift exponent rate =
  Expected.normalizedConstantRateIsRate
    rate (zipfPNFAtoms n shift exponent)
    (zipfPNFAtomsNormalize n shift exponent)


------------------------------------------------------------------------
-- F13 snowball: specialize the constructed PNF law to the ALREADY-OWNED
-- two-rank IID collision theorem. No alternative collision framework.
-- For support 2: rank index 1 precedes index 0 in the fold.
------------------------------------------------------------------------

twoRankP : Nat → Nat → ℚ
twoRankP shift exponent =
  rawTerm (suc zero) shift exponent *
  inverseNormalizer (suc zero) shift exponent

twoRankQ : Nat → Nat → ℚ
twoRankQ shift exponent =
  rawTerm zero shift exponent *
  inverseNormalizer (suc zero) shift exponent

twoRankPPositive : ∀ shift exponent → R.Positive (twoRankP shift exponent)
twoRankPPositive shift exponent =
  ℚP.pos*pos⇒pos
    (rawTerm (suc zero) shift exponent)
    (inverseNormalizer (suc zero) shift exponent)
    {{rawTermPositive (suc zero) shift exponent}}
    {{inverseNormalizerPositive (suc zero) shift exponent}}

twoRankQPositive : ∀ shift exponent → R.Positive (twoRankQ shift exponent)
twoRankQPositive shift exponent =
  ℚP.pos*pos⇒pos
    (rawTerm zero shift exponent)
    (inverseNormalizer (suc zero) shift exponent)
    {{rawTermPositive zero shift exponent}}
    {{inverseNormalizerPositive (suc zero) shift exponent}}

twoRankPNormalized : ∀ shift exponent →
  twoRankP shift exponent + twoRankQ shift exponent ≡ 1ℚ
twoRankPNormalized shift exponent =
  trans
    (cong (twoRankP shift exponent +_)
      (sym (ℚP.+-identityʳ (twoRankQ shift exponent))))
    (zipfPNFAtomsNormalize (suc zero) shift exponent)

twoRankZipfIIDLaw : Nat → Nat → Adapter.TwoRankIIDLaw
twoRankZipfIIDLaw shift exponent =
  Adapter.two-rank-iid-law
    (twoRankP shift exponent)
    (twoRankQ shift exponent)
    (ℚP.nonNegative⁻¹ (twoRankP shift exponent)
      {{ℚP.pos⇒nonNeg (twoRankP shift exponent)
        {{twoRankPPositive shift exponent}}}})
    (ℚP.nonNegative⁻¹ (twoRankQ shift exponent)
      {{ℚP.pos⇒nonNeg (twoRankQ shift exponent)
        {{twoRankQPositive shift exponent}}}})
    (twoRankPNormalized shift exponent)
    "IID with replacement on constructed finite 2-rank Zipf"

twoRankZipfCollisionIdentity : ∀ shift exponent →
  Adapter.iidTwoDrawMeanDistinct (twoRankZipfIIDLaw shift exponent)
  + Adapter.iidTwoDrawCollision (twoRankZipfIIDLaw shift exponent)
  ≡ Adapter.twoℚ
twoRankZipfCollisionIdentity shift exponent =
  Adapter.iidTwoDrawMeanPlusCollisionIsTwo
    (twoRankZipfIIDLaw shift exponent)
