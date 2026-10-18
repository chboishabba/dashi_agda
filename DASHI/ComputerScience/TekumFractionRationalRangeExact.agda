module DASHI.ComputerScience.TekumFractionRationalRangeExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _*_)
open import Data.Integer.Base as ℤ using (ℤ; +_; -_; _*_; _≤_; _<_)
import Data.Integer.Properties as ℤP
open import Data.Nat.Base using (NonZero; _<_)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base as ℚ using (ℚ; ½; -½; _/_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Unnormalised.Base as ℚᵘ
  using (ℚᵘ; ½; -½; _/_; _<_)
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Relation.Binary.PropositionalEquality.≡-Reasoning

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.ComputerScience.TekumFractionRangeExact as Range

------------------------------------------------------------------------
-- The centered denominator is written syntactically as suc (2 A_p).  By the
-- already-proved A003462 identity this is exactly 3^p.  This presentation
-- makes the strict half bound a direct cross-product theorem and avoids any
-- dependence on gcd normalization internals.
------------------------------------------------------------------------

fractionDenominator : Nat → Nat
fractionDenominator p = suc (2 * Positional.center p)

fractionDenominatorIsPowerThree :
  (p : Nat) →
  fractionDenominator p ≡ BT.pow3 p
fractionDenominatorIsPowerThree p =
  Range.twiceCenterPlusOneIsPowerThree p

fractionDenominatorNonZero :
  (p : Nat) → NonZero (fractionDenominator p)
fractionDenominatorNonZero p = _

fractionNumerator :
  ∀ {p} → Vec Trit.Trit p → ℤ
fractionNumerator fraction = BT.toInteger (BT.eval fraction)

------------------------------------------------------------------------
-- Cross-product inequalities:  -(2A+1) < 2I(F) < 2A+1.
------------------------------------------------------------------------

centerTimesTwoStrictDenominator :
  (p : Nat) →
  Positional.center p * 2 < fractionDenominator p
centerTimesTwoStrictDenominator p =
  NatP.s≤s (NatP.≤-reflexive (NatP.*-comm (Positional.center p) 2))

fractionTwiceUpperInteger :
  ∀ {p} (fraction : Vec Trit.Trit p) →
  fractionNumerator fraction ℤ.* (+ 2)
  ℤ.< + (fractionDenominator p)
fractionTwiceUpperInteger {p} fraction =
  ℤP.≤-<-trans scaledUpper strictCenter
  where
  scaledUpper :
    fractionNumerator fraction ℤ.* (+ 2)
    ℤ.≤ (+ (Positional.center p)) ℤ.* (+ 2)
  scaledUpper =
    ℤP.*-monoʳ-≤-nonNeg (+ 2) (Range.fractionIntegerUpper fraction)

  strictCenter :
    (+ (Positional.center p)) ℤ.* (+ 2)
    ℤ.< + (fractionDenominator p)
  strictCenter
    rewrite ℤP.pos-* (Positional.center p) 2 =
    ℤ.+<+ (centerTimesTwoStrictDenominator p)

fractionTwiceLowerInteger :
  ∀ {p} (fraction : Vec Trit.Trit p) →
  ℤ.- (+ (fractionDenominator p))
  ℤ.< fractionNumerator fraction ℤ.* (+ 2)
fractionTwiceLowerInteger {p} fraction =
  ℤP.<-≤-trans strictCenter scaledLower
  where
  scaledLower :
    (ℤ.- (+ (Positional.center p))) ℤ.* (+ 2)
    ℤ.≤ fractionNumerator fraction ℤ.* (+ 2)
  scaledLower =
    ℤP.*-monoʳ-≤-nonNeg (+ 2) (Range.fractionIntegerLower fraction)

  positiveCenter :
    (+ (Positional.center p)) ℤ.* (+ 2)
    ℤ.< + (fractionDenominator p)
  positiveCenter
    rewrite ℤP.pos-* (Positional.center p) 2 =
    ℤ.+<+ (centerTimesTwoStrictDenominator p)

  strictCenter :
    ℤ.- (+ (fractionDenominator p))
    ℤ.< (ℤ.- (+ (Positional.center p))) ℤ.* (+ 2)
  strictCenter =
    begin-strict
      ℤ.- (+ (fractionDenominator p))
        <⟨ ℤP.neg-mono-< positiveCenter ⟩
      ℤ.- ((+ (Positional.center p)) ℤ.* (+ 2))
        ≡⟨ ℤP.neg-distribˡ-* (+ (Positional.center p)) (+ 2) ⟩
      (ℤ.- (+ (Positional.center p))) ℤ.* (+ 2)
    ∎
    where open ℤP.≤-Reasoning

------------------------------------------------------------------------
-- Raw and canonical rational forms.
------------------------------------------------------------------------

rawFraction :
  ∀ {p} → Vec Trit.Trit p → ℚᵘ
rawFraction {p} fraction =
  let instance denominatorNonZero = fractionDenominatorNonZero p
  in fractionNumerator fraction ℚᵘ./ fractionDenominator p

canonicalFraction :
  ∀ {p} → Vec Trit.Trit p → ℚ
canonicalFraction fraction = ℚ.fromℚᵘ (rawFraction fraction)

rawFractionLower :
  ∀ {p} (fraction : Vec Trit.Trit p) →
  ℚᵘ.-½ ℚᵘ.< rawFraction fraction
rawFractionLower {p} fraction =
  ℚᵘ.*<* rawCross
  where
  rawCross :
    (ℤ.- (+ 1)) ℤ.* (+ (fractionDenominator p))
    ℤ.< fractionNumerator fraction ℤ.* (+ 2)
  rawCross =
    begin-strict
      (ℤ.- (+ 1)) ℤ.* (+ (fractionDenominator p))
        ≡⟨ ℤP.-1*i≡-i (+ (fractionDenominator p)) ⟩
      ℤ.- (+ (fractionDenominator p))
        <⟨ fractionTwiceLowerInteger fraction ⟩
      fractionNumerator fraction ℤ.* (+ 2)
    ∎
    where open ℤP.≤-Reasoning

rawFractionUpper :
  ∀ {p} (fraction : Vec Trit.Trit p) →
  rawFraction fraction ℚᵘ.< ℚᵘ.½
rawFractionUpper {p} fraction =
  ℚᵘ.*<* rawCross
  where
  rawCross :
    fractionNumerator fraction ℤ.* (+ 2)
    ℤ.< (+ 1) ℤ.* (+ (fractionDenominator p))
  rawCross =
    begin-strict
      fractionNumerator fraction ℤ.* (+ 2)
        <⟨ fractionTwiceUpperInteger fraction ⟩
      + (fractionDenominator p)
        ≡⟨ sym (ℤP.*-identityˡ (+ (fractionDenominator p))) ⟩
      (+ 1) ℤ.* (+ (fractionDenominator p))
    ∎
    where open ℤP.≤-Reasoning

rawFractionStrictHalfBound :
  ∀ {p} (fraction : Vec Trit.Trit p) →
  (ℚᵘ.-½ ℚᵘ.< rawFraction fraction)
  × (rawFraction fraction ℚᵘ.< ℚᵘ.½)
rawFractionStrictHalfBound fraction =
  rawFractionLower fraction , rawFractionUpper fraction

canonicalNegativeHalf : ℚ
canonicalNegativeHalf = ℚ.fromℚᵘ ℚᵘ.-½

canonicalPositiveHalf : ℚ
canonicalPositiveHalf = ℚ.fromℚᵘ ℚᵘ.½

canonicalNegativeHalfIsBuiltin : canonicalNegativeHalf ≡ ℚ.-½
canonicalNegativeHalfIsBuiltin = refl

canonicalPositiveHalfIsBuiltin : canonicalPositiveHalf ≡ ℚ.½
canonicalPositiveHalfIsBuiltin = refl

canonicalLower :
  ∀ {p} (fraction : Vec Trit.Trit p) →
  canonicalNegativeHalf ℚ.< canonicalFraction fraction
canonicalLower fraction =
  ℚP.toℚᵘ-cancel-< transported
  where
  leftEquivalent = ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ ℚᵘ.-½)
  rightEquivalent = ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ (rawFraction fraction))

  leftTransport :
    ℚ.toℚᵘ canonicalNegativeHalf ℚᵘ.< rawFraction fraction
  leftTransport =
    ℚᵘP.<-respˡ-≃ leftEquivalent (rawFractionLower fraction)

  transported :
    ℚ.toℚᵘ canonicalNegativeHalf
    ℚᵘ.< ℚ.toℚᵘ (canonicalFraction fraction)
  transported =
    ℚᵘP.<-respʳ-≃ rightEquivalent leftTransport

canonicalUpper :
  ∀ {p} (fraction : Vec Trit.Trit p) →
  canonicalFraction fraction ℚ.< canonicalPositiveHalf
canonicalUpper fraction =
  ℚP.toℚᵘ-cancel-< transported
  where
  leftEquivalent = ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ (rawFraction fraction))
  rightEquivalent = ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ ℚᵘ.½)

  leftTransport :
    ℚ.toℚᵘ (canonicalFraction fraction) ℚᵘ.< ℚᵘ.½
  leftTransport =
    ℚᵘP.<-respˡ-≃ leftEquivalent (rawFractionUpper fraction)

  transported :
    ℚ.toℚᵘ (canonicalFraction fraction)
    ℚᵘ.< ℚ.toℚᵘ canonicalPositiveHalf
  transported =
    ℚᵘP.<-respʳ-≃ rightEquivalent leftTransport

fractionStrictHalfBound :
  ∀ {p} (fraction : Vec Trit.Trit p) →
  (ℚ.-½ ℚ.< canonicalFraction fraction)
  × (canonicalFraction fraction ℚ.< ℚ.½)
fractionStrictHalfBound fraction
  rewrite sym canonicalNegativeHalfIsBuiltin
        | sym canonicalPositiveHalfIsBuiltin =
  canonicalLower fraction , canonicalUpper fraction

canonicalFractionIsSignedDivision :
  ∀ {p} (fraction : Vec Trit.Trit p) →
  canonicalFraction fraction
  ≡ let instance denominatorNonZero = fractionDenominatorNonZero p
    in fractionNumerator fraction ℚ./ fractionDenominator p
canonicalFractionIsSignedDivision fraction = refl
