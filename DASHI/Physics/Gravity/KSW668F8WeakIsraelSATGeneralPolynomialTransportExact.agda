module DASHI.Physics.Gravity.KSW668F8WeakIsraelSATGeneralPolynomialTransportExact where

------------------------------------------------------------------------
-- XXIX G2: original weak-Israel SAT source polynomial at ANY rational v.
-- The original scheme has target satisfying
--   (v-1) target = 2 amp S - (1+v) P.
-- Actual SAT correction to M RHS is
--   2(1-v)/dy * (target - M).
--
-- Avoid variable division: multiply SAT by dy to get exact numerator
--   dy * SAT = -4 amp S +2(1+v)P -2(1-v)M.
-- This holds for arbitrary rational v, source S, amplitude, P, M and
-- any target satisfying the original source equation.
--
-- No assertion that the finite wall target enforces its continuum
-- trace, or that the full coupled (U,P,M) SSPRK3 energy is stable.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

two four : ℚ
two = (+ 2) / 1
four = (+ 4) / 1

wallSourceEquationRHS : ℚ → ℚ → ℚ → ℚ → ℚ
wallSourceEquationRHS v amp src p =
  two * amp * src + - ((1ℚ + v) * p)

satNumerator : ℚ → ℚ → ℚ → ℚ
satNumerator v target m =
  two * (1ℚ + - v) * (target + - m)

satExpanded : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
satExpanded v amp src p m =
  - (four * amp * src)
    + two * (1ℚ + v) * p
    + - (two * (1ℚ + - v) * m)

originalSATNoDivision :
  (v amp src p m target : ℚ) →
  ((v + - 1ℚ) * target ≡ wallSourceEquationRHS v amp src p) →
  satNumerator v target m ≡ satExpanded v amp src p m
originalSATNoDivision v amp src p m target targetIsIsrael =
  trans
    (solve [])
    (trans
      (cong
        (λ x → - (two * x) + - (two * (1ℚ + - v) * m))
        targetIsIsrael)
      (solve []))
