module DASHI.ComputerScience.TekumFractionInjectiveExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base as ℤ using (+_; _*_)
import Data.Integer.Properties as ℤP
import Data.Rational.Properties as ℚP
open import Data.Rational.Unnormalised.Base as ℚᵘ using (_≃_)
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import Data.Vec using (Vec)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.ComputerScience.TekumFractionRationalRangeExact as Fraction

------------------------------------------------------------------------
-- FIXED-WIDTH FRACTION INJECTIVITY
--
-- For fixed p the source fraction map is F ↦ I_p(F)/3^p.  Equality in the
-- canonical rational carrier is transported back to the unnormalised setoid;
-- cross multiplication then has the same nonzero denominator on both sides.
------------------------------------------------------------------------

canonicalFractionEqualityToRaw :
  ∀ {p} {x y : Vec Trit.Trit p} →
  Fraction.canonicalFraction x ≡ Fraction.canonicalFraction y →
  Fraction.rawFraction x ℚᵘ.≃ Fraction.rawFraction y
canonicalFractionEqualityToRaw {x = x} {y = y} eq =
  ℚᵘP.≃-trans
    (ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ (Fraction.rawFraction x)))
    (ℚᵘP.≃-trans
      (ℚP.toℚᵘ-cong eq)
      (ℚP.toℚᵘ-fromℚᵘ (Fraction.rawFraction y)))

fractionNumeratorEquality :
  ∀ {p} {x y : Vec Trit.Trit p} →
  Fraction.canonicalFraction x ≡ Fraction.canonicalFraction y →
  BT.toInteger (BT.eval x) ≡ BT.toInteger (BT.eval y)
fractionNumeratorEquality {p} {x} {y} eq =
  ℤP.*-cancelʳ-≡
    (BT.toInteger (BT.eval x))
    (BT.toInteger (BT.eval y))
    (+ (Fraction.fractionDenominator p))
    cross
  where
  rawEq = canonicalFractionEqualityToRaw eq

  cross :
    BT.toInteger (BT.eval x) ℤ.* (+ (Fraction.fractionDenominator p))
    ≡ BT.toInteger (BT.eval y) ℤ.* (+ (Fraction.fractionDenominator p))
  cross = ℚᵘP.drop-*≡* rawEq

canonicalFractionInjective :
  ∀ {p} {x y : Vec Trit.Trit p} →
  Fraction.canonicalFraction x ≡ Fraction.canonicalFraction y →
  x ≡ y
canonicalFractionInjective eq =
  Positional.toIntegerInjective (fractionNumeratorEquality eq)
