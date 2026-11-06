{-# OPTIONS --safe #-}
module DASHI.Foundations.BishopCayleyRationalDifferentialEquationExact where

------------------------------------------------------------------------
-- ORIGINAL Q[i] CAYLEY DIFFERENTIAL EQUATION, ALL RATIONAL t.
--
-- Reuse the ORIGINAL Cayley parameterization and Cayley-Dickson
-- rational complex multiplication. Let N(t)=(1-t²)+2it,
-- D(t)=1+t², and C(t)=N(t)/D(t). The quotient-rule numerator obeys
--
--        N'(t) D(t) - N(t) D'(t) = 2i N(t)
--
-- EXACTLY as a universal Gaussian polynomial, so, wherever D(t)
-- is nonzero, C'(t)=2i*C(t)/(1+t²).
--
-- This is the polynomial differential equation needed to match
-- C(t) with exp_C(2i*atan_B(t)). Unlike a numerical Cayley check,
-- it is an ALL-parameter theorem, with no division or exceptional
-- denominator. It is NOT a Bishop analytic derivative theorem:
-- original atan/exp termwise differentiation and constructive
-- uniqueness still require their native source proofs.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as Q using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as QRing

import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as CD
import DASHI.Foundations.BishopMachinExistingCayleyReuseExact as Cayley

two : ℚ
two = + 2 / 1

nativeImaginaryTwo : CD.RationalComplex
nativeImaginaryTwo = CD.complex 0ℚ two

cayleyNumeratorDerivative : ℚ → CD.RationalComplex
cayleyNumeratorDerivative t =
  CD.complex (0ℚ - (two * t)) two

cayleyDenominatorDerivative : ℚ → ℚ
cayleyDenominatorDerivative t = two * t

scalarComplex : ℚ → CD.RationalComplex
scalarComplex x = CD.complex x 0ℚ

cayleyQuotientNumeratorCross : ℚ → CD.RationalComplex
cayleyQuotientNumeratorCross t =
  CD._-c_
    (CD._*c_
      (cayleyNumeratorDerivative t)
      (scalarComplex (Cayley.cayleyDenominator t)))
    (CD._*c_
      (Cayley.cayleyNumerator t)
      (scalarComplex (cayleyDenominatorDerivative t)))

cayleyODErightNumerator : ℚ → CD.RationalComplex
cayleyODErightNumerator t =
  CD._*c_ nativeImaginaryTwo (Cayley.cayleyNumerator t)

cayleyQuotientDifferentialPolynomialExact :
  (t : ℚ) →
  cayleyQuotientNumeratorCross t ≡ cayleyODErightNumerator t
cayleyQuotientDifferentialPolynomialExact t =
  CD.complexExt QRing.solve-∀ QRing.solve-∀

-- The same original numerator and denominator satisfy the norm
-- equation |N|²=D². The finite ODE and norm certificates therefore
-- agree about the actual unit-circle Cayley carrier.
cayleyNumeratorNormIsDenominatorSquared :
  (t : ℚ) →
  CD.complexNormSq (Cayley.cayleyNumerator t)
  ≡ Cayley.cayleyDenominator t * Cayley.cayleyDenominator t
cayleyNumeratorNormIsDenominatorSquared =
  Cayley.cayleyNumeratorPythagorean
