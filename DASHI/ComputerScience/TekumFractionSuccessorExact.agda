module DASHI.ComputerScience.TekumFractionSuccessorExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; _+_; _*_; _<_ ; +<+; -<+; -<-)
import Data.Integer.Properties as ℤP
open import Data.Nat.Base using (z<s)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _+_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Unnormalised.Base as ℚᵘ using (_<_)
import Data.Rational.Unnormalised.Properties as ℚᵘP
open import Data.Vec using (Vec)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Algebra.Trit as Trit
import DASHI.ComputerScience.TekumBalancedSuccessorExact as Succ
import DASHI.ComputerScience.TekumFractionRationalRangeExact as Fraction
import DASHI.ComputerScience.TekumSignificandRangeExact as Sig

------------------------------------------------------------------------
-- CASE 1 OF HUNHOLD PROP. 4
--
-- If the balanced successor stops inside the fraction field, its exact integer
-- numerator increases by one while the denominator 3^p is unchanged. Hence the
-- canonical rational fraction, and therefore 1+f, strictly increases.
------------------------------------------------------------------------

integerAddOneStrict : (z : ℤ) → z ℤ.< z ℤ.+ (+ 1)
integerAddOneStrict (+ n) = +<+ (Data.Nat.Properties.n<1+n n)
integerAddOneStrict -[1+ 0 ] = -<+
integerAddOneStrict -[1+ Data.Nat.Base.suc n ] =
  -<- (Data.Nat.Properties.n<1+n n)

rawFractionSuccessorStrict :
  ∀ {p} {fraction : Vec Trit.Trit p} →
  Succ.HasSuccessor fraction →
  Fraction.rawFraction fraction
    ℚᵘ.< Fraction.rawFraction (Succ.successorWord fraction)
rawFractionSuccessorStrict {p} {fraction} carry =
  ℚᵘ.*<* rawCross
  where
  denominator = Fraction.fractionDenominator p

  numeratorStep :
    Fraction.fractionNumerator (Succ.successorWord fraction)
    ≡ Fraction.fractionNumerator fraction ℤ.+ (+ 1)
  numeratorStep = Succ.successorInteger carry

  rawCross :
    Fraction.fractionNumerator fraction ℤ.* (+ denominator)
    ℤ.<
    Fraction.fractionNumerator (Succ.successorWord fraction) ℤ.* (+ denominator)
  rawCross =
    subst
      (λ z →
        Fraction.fractionNumerator fraction ℤ.* (+ denominator)
        ℤ.< z ℤ.* (+ denominator))
      (Relation.Binary.PropositionalEquality.sym numeratorStep)
      (ℤP.*-monoʳ-<-pos (+ denominator)
        (integerAddOneStrict (Fraction.fractionNumerator fraction)))

canonicalFractionSuccessorStrict :
  ∀ {p} {fraction : Vec Trit.Trit p} →
  Succ.HasSuccessor fraction →
  Fraction.canonicalFraction fraction
    ℚ.< Fraction.canonicalFraction (Succ.successorWord fraction)
canonicalFractionSuccessorStrict {fraction = fraction} carry =
  ℚP.toℚᵘ-cancel-< transported
  where
  leftEquivalent =
    ℚᵘP.≃-sym
      (ℚP.toℚᵘ-fromℚᵘ (Fraction.rawFraction fraction))
  rightEquivalent =
    ℚᵘP.≃-sym
      (ℚP.toℚᵘ-fromℚᵘ
        (Fraction.rawFraction (Succ.successorWord fraction)))

  leftTransport :
    ℚ.toℚᵘ (Fraction.canonicalFraction fraction)
    ℚᵘ.< Fraction.rawFraction (Succ.successorWord fraction)
  leftTransport =
    ℚᵘP.<-respˡ-≃ leftEquivalent
      (rawFractionSuccessorStrict carry)

  transported :
    ℚ.toℚᵘ (Fraction.canonicalFraction fraction)
    ℚᵘ.< ℚ.toℚᵘ
      (Fraction.canonicalFraction (Succ.successorWord fraction))
  transported =
    ℚᵘP.<-respʳ-≃ rightEquivalent leftTransport

significandSuccessorStrict :
  ∀ {p} {fraction : Vec Trit.Trit p} →
  Succ.HasSuccessor fraction →
  Sig.significand fraction
    ℚ.< Sig.significand (Succ.successorWord fraction)
significandSuccessorStrict carry =
  ℚP.+-monoʳ-< 1ℚ (canonicalFractionSuccessorStrict carry)
