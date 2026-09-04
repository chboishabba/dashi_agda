module DASHI.Analysis.BernoulliFourCubicFiniteDifferenceExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

------------------------------------------------------------------------
-- EXACT FINITE-DIFFERENCE ORIGIN OF THE CUBIC BERNOULLI COEFFICIENT
--
-- B4(x) = x^4 - 2 x^3 + x^2 - 1/30
--
-- and exactly
--
--   B4(x + 1) - B4(x) = 4 x^3.
--
-- This is pure rational polynomial algebra.  It does NOT prove analytic
-- continuation of zeta, but it closes the finite algebra explaining why B4 is
-- the Bernoulli polynomial attached to the cubic longitudinal sum.
------------------------------------------------------------------------

two : ℚ
two = 1ℚ + 1ℚ

four : ℚ
four = two + two

oneThirtieth : ℚ
oneThirtieth = + 1 / 30

square : ℚ → ℚ
square x = x * x

cube : ℚ → ℚ
cube x = square x * x

fourth : ℚ → ℚ
fourth x = square x * square x

bernoulliFourPolynomial : ℚ → ℚ
bernoulliFourPolynomial x =
  ((fourth x - (two * cube x)) + square x) - oneThirtieth

bernoulliFourFiniteDifferenceIsFourCubes :
  (x : ℚ) →
  bernoulliFourPolynomial (x + 1ℚ) - bernoulliFourPolynomial x
  ≡ four * cube x
bernoulliFourFiniteDifferenceIsFourCubes x =
  ℚRing.solve (x ∷ [])

record CubicBernoulliFiniteDifferenceReceipt : Set where
  field
    x : ℚ
    finiteDifference : ℚ
    finiteDifferenceLaw :
      finiteDifference ≡
      bernoulliFourPolynomial (x + 1ℚ) - bernoulliFourPolynomial x
    cubicLaw : finiteDifference ≡ four * cube x

open CubicBernoulliFiniteDifferenceReceipt public

buildCubicBernoulliFiniteDifferenceReceipt :
  (x : ℚ) → CubicBernoulliFiniteDifferenceReceipt
buildCubicBernoulliFiniteDifferenceReceipt x = record
  { x = x
  ; finiteDifference =
      bernoulliFourPolynomial (x + 1ℚ) - bernoulliFourPolynomial x
  ; finiteDifferenceLaw = refl
  ; cubicLaw = bernoulliFourFiniteDifferenceIsFourCubes x
  }

data FiniteDifferenceAutomaticallyProvesZetaContinuation : Set where

finiteBernoulliAlgebraIsNotAnalyticContinuation :
  FiniteDifferenceAutomaticallyProvesZetaContinuation → DASHI.Core.Prelude.⊥
finiteBernoulliAlgebraIsNotAnalyticContinuation ()
