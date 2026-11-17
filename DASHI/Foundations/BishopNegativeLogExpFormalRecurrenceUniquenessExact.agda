{-# OPTIONS --safe #-}
module DASHI.Foundations.BishopNegativeLogExpFormalRecurrenceUniquenessExact where

------------------------------------------------------------------------
-- K04d-LOG: UNIVERSAL FINITE COEFFICIENT UNIQUENESS.
--
-- Let F(X) = exp(-sum_(k>=1) X^k/k) = sum a_n X^n in Q[[X]].
-- Its formal differential equation (1-X)F'(X)+F(X)=0 yields
--
--   (n+1) a_(n+1) + (1-n) a_n = 0.
--
-- Equivalently, for n>=0:
--   a_(n+2) = (n/(n+2)) a_(n+1).
--
-- This module proves constructively that every rational coefficient
-- history with this *solved recurrence* and a_0=1, a_1=-1 equals the
-- canonical coefficients of 1-X. No finite degree cutoff and no
-- numerical regression is used.
--
-- Critical boundary: identifying the coefficients of the ORIGINAL
-- nested exp/log composition with this recurrence, and transporting
-- the resulting formal identity through absolutely convergent
-- BISHOP series, are separate open proof obligations. This module
-- cannot discharge them by choosing a synthetic coefficient history.
--
-- Newton formal series; Bishop/Bridges; Murray/Csimma.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; cong; sym)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _/_; _*_; _-_)
import Data.Rational.Properties as ℚP

zeroQ oneQ minusOneQ : ℚ
zeroQ = + 0 / 1
oneQ = + 1 / 1
minusOneQ = (+ 0 / 1) - (+ 1 / 1)

successorFactor : Nat → ℚ
successorFactor n = + n / suc (suc n)

canonicalCoefficient : Nat → ℚ
canonicalCoefficient zero = oneQ
canonicalCoefficient (suc zero) = minusOneQ
canonicalCoefficient (suc (suc _)) = zeroQ

record FormalLogExpSolvedRecurrence (a : Nat → ℚ) : Set where
  field
    constantOne : a zero ≡ oneQ
    linearMinusOne : a (suc zero) ≡ minusOneQ
    solvedRecurrence :
      (n : Nat) →
      a (suc (suc n)) ≡
      successorFactor n * a (suc n)

open FormalLogExpSolvedRecurrence public

canonicalSolvedRecurrence :
  FormalLogExpSolvedRecurrence canonicalCoefficient
canonicalSolvedRecurrence = record
  { constantOne = refl
  ; linearMinusOne = refl
  ; solvedRecurrence = λ
      { zero →
          sym
            (trans
              (cong (λ q → q * minusOneQ)
                (ℚP.0/n≡0 (suc (suc zero))))
              (ℚP.*-zeroˡ minusOneQ))
      ; (suc n) →
          sym (ℚP.*-zeroʳ (successorFactor (suc n)))
      }
  }

tailCoefficientsZero :
  (a : Nat → ℚ) →
  FormalLogExpSolvedRecurrence a →
  (n : Nat) →
  a (suc (suc n)) ≡ zeroQ
tailCoefficientsZero a evidence zero =
  trans
    (solvedRecurrence evidence zero)
    (trans
      (cong (λ q → q * a (suc zero))
        (ℚP.0/n≡0 (suc (suc zero))))
      (ℚP.*-zeroˡ (a (suc zero))))
tailCoefficientsZero a evidence (suc n) =
  trans
    (solvedRecurrence evidence (suc n))
    (trans
      (cong (λ q → successorFactor (suc n) * q)
        (tailCoefficientsZero a evidence n))
      (ℚP.*-zeroʳ (successorFactor (suc n))))

allFormalCoefficientsCanonical :
  (a : Nat → ℚ) →
  FormalLogExpSolvedRecurrence a →
  (n : Nat) →
  a n ≡ canonicalCoefficient n
allFormalCoefficientsCanonical a evidence zero =
  constantOne evidence
allFormalCoefficientsCanonical a evidence (suc zero) =
  linearMinusOne evidence
allFormalCoefficientsCanonical a evidence (suc (suc n)) =
  tailCoefficientsZero a evidence n
