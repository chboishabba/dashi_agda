module DASHI.ComputerScience.TekumSignificandRangeExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; ½; -½; _+_; _*_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve-∀)
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumFractionRationalRangeExact as Fraction

------------------------------------------------------------------------
-- Exact source significand band.
--
-- Hunhold writes ordinary values as s (1+f) 3^e with -1/2 < f < 1/2.
-- The fraction theorem is already on canonical ℚ, so this owner closes the
-- strict significand interval without introducing an ambient real carrier.
------------------------------------------------------------------------

significand :
  ∀ {p} → Vec Trit.Trit p → ℚ
significand fraction = 1ℚ + Fraction.canonicalFraction fraction

threeHalves : ℚ
threeHalves = 1ℚ + ½

three : ℚ
three = 1ℚ + 1ℚ + 1ℚ

onePlusNegativeHalfIsHalf :
  1ℚ + (-½) ≡ ½
onePlusNegativeHalfIsHalf = solve-∀

halfBelowSignificand :
  ∀ {p} (fraction : Vec Trit.Trit p) →
  ½ ℚ.< significand fraction
halfBelowSignificand fraction
  with Fraction.fractionStrictHalfBound fraction
... | lower , upper =
  subst
    (λ left → left ℚ.< significand fraction)
    onePlusNegativeHalfIsHalf
    (ℚP.+-monoʳ-< 1ℚ lower)

significandBelowThreeHalves :
  ∀ {p} (fraction : Vec Trit.Trit p) →
  significand fraction ℚ.< threeHalves
significandBelowThreeHalves fraction
  with Fraction.fractionStrictHalfBound fraction
... | lower , upper = ℚP.+-monoʳ-< 1ℚ upper

significandStrictBand :
  ∀ {p} (fraction : Vec Trit.Trit p) →
  (½ ℚ.< significand fraction)
  × (significand fraction ℚ.< threeHalves)
significandStrictBand fraction =
  halfBelowSignificand fraction , significandBelowThreeHalves fraction

nextExponentLowerEqualsCurrentUpper :
  three * ½ ≡ threeHalves
nextExponentLowerEqualsCurrentUpper = solve-∀
