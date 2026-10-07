module DASHI.ComputerScience.TekumFractionOrderExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base as ℤ using (+_; _*_; _<_)
import Data.Integer.Properties as ℤP
open import Data.Rational.Base as ℚ using (1ℚ; _+_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Unnormalised.Base as ℚᵘ using (_<_)
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumFractionRationalRangeExact as Fraction
import DASHI.ComputerScience.TekumSignificandRangeExact as Sig

------------------------------------------------------------------------
-- ARBITRARY SAME-WIDTH FRACTION ORDER
--
-- The earlier successor owner pays the adjacent case needed by the carry
-- proof.  Proposition 4 for arbitrary code gaps also needs the direct fact
-- that strict centered-integer order of two same-width fraction fields is
-- exactly strict rational/significand order.  This owner pays that numerical
-- compiler once, with no source-code or parser assumptions.
------------------------------------------------------------------------

rawFractionIntegerStrict :
  ∀ {p} {left right : Vec Trit.Trit p} →
  Fraction.fractionNumerator left ℤ.< Fraction.fractionNumerator right →
  Fraction.rawFraction left ℚᵘ.< Fraction.rawFraction right
rawFractionIntegerStrict {p} {left} {right} numeratorLt =
  ℚᵘP.*<* rawCross
  where
  denominator = Fraction.fractionDenominator p

  rawCross :
    Fraction.fractionNumerator left ℤ.* (+ denominator)
    ℤ.< Fraction.fractionNumerator right ℤ.* (+ denominator)
  rawCross =
    ℤP.*-monoʳ-<-pos (+ denominator) numeratorLt

canonicalFractionIntegerStrict :
  ∀ {p} {left right : Vec Trit.Trit p} →
  Fraction.fractionNumerator left ℤ.< Fraction.fractionNumerator right →
  Fraction.canonicalFraction left ℚ.< Fraction.canonicalFraction right
canonicalFractionIntegerStrict {left = left} {right = right} numeratorLt =
  ℚP.toℚᵘ-cancel-< transported
  where
  leftEquivalent =
    ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ (Fraction.rawFraction left))
  rightEquivalent =
    ℚᵘP.≃-sym (ℚP.toℚᵘ-fromℚᵘ (Fraction.rawFraction right))

  leftTransport :
    ℚ.toℚᵘ (Fraction.canonicalFraction left)
    ℚᵘ.< Fraction.rawFraction right
  leftTransport =
    ℚᵘP.<-respˡ-≃ leftEquivalent
      (rawFractionIntegerStrict numeratorLt)

  transported :
    ℚ.toℚᵘ (Fraction.canonicalFraction left)
    ℚᵘ.< ℚ.toℚᵘ (Fraction.canonicalFraction right)
  transported =
    ℚᵘP.<-respʳ-≃ rightEquivalent leftTransport

significandIntegerStrict :
  ∀ {p} {left right : Vec Trit.Trit p} →
  Fraction.fractionNumerator left ℤ.< Fraction.fractionNumerator right →
  Sig.significand left ℚ.< Sig.significand right
significandIntegerStrict numeratorLt =
  ℚP.+-monoʳ-< 1ℚ (canonicalFractionIntegerStrict numeratorLt)
