module DASHI.Physics.Closure.NSTriadKNLuoBernsteinExponentCalibrationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Calibrate the exact exponents used when the existing finite cube Bernstein
-- theorem is presented in dyadic notation.  In dimension three, the L2-to-L∞
-- exponent is 3/2.  One spatial derivative adds one, giving 5/2.  Squaring
-- those inequalities produces integer dyadic exponents three and five.
--
-- This module deliberately does not identify those exponents with the
-- project-specific Schur profile (1/4)^j (1/32)^d.  That later comparison is
-- an independently proved envelope theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _*_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

one half threeHalves fiveHalves two three five : ℚ
one = 1ℚ
half = Int.+ 1 / 2
threeHalves = Int.+ 3 / 2
fiveHalves = Int.+ 5 / 2
two = Int.+ 2 / 1
three = Int.+ 3 / 1
five = Int.+ 5 / 1

threeDimensionalBernsteinExponent :
  three * half ≡ threeHalves
threeDimensionalBernsteinExponent = solve []

derivativeAddsOneExponent :
  threeHalves + one ≡ fiveHalves
derivativeAddsOneExponent = solve []

squaredBernsteinExponent :
  two * threeHalves ≡ three
squaredBernsteinExponent = solve []

squaredDerivativeBernsteinExponent :
  two * fiveHalves ≡ five
squaredDerivativeBernsteinExponent = solve []

combinedExponentCalibration :
  two * (three * half + one) ≡ five
combinedExponentCalibration = solve []

record BernsteinScalePresentation : Set where
  constructor bernstein-scale-presentation
  field
    shellIndex : ℚ
    l2ToLInfinityExponent derivativeLInfinityExponent : ℚ

    l2ExponentMeaning :
      l2ToLInfinityExponent ≡ threeHalves * shellIndex

    derivativeExponentMeaning :
      derivativeLInfinityExponent
      ≡ l2ToLInfinityExponent + shellIndex

open BernsteinScalePresentation public

squaredL2ExponentMeaning :
  (presentation : BernsteinScalePresentation) →
  two * l2ToLInfinityExponent presentation
  ≡ three * shellIndex presentation
squaredL2ExponentMeaning presentation
  rewrite l2ExponentMeaning presentation =
  solve (shellIndex presentation ∷ [])

squaredDerivativeExponentMeaning :
  (presentation : BernsteinScalePresentation) →
  two * derivativeLInfinityExponent presentation
  ≡ five * shellIndex presentation
squaredDerivativeExponentMeaning presentation
  rewrite derivativeExponentMeaning presentation
        | l2ExponentMeaning presentation =
  solve (shellIndex presentation ∷ [])

bernsteinExponentCalibrationClosed : Bool
bernsteinExponentCalibrationClosed = true

schurExponentIdentificationKeptSeparate : Bool
schurExponentIdentificationKeptSeparate = true

bernsteinExponentCalibrationClosedIsTrue :
  bernsteinExponentCalibrationClosed ≡ true
bernsteinExponentCalibrationClosedIsTrue = refl

schurExponentIdentificationKeptSeparateIsTrue :
  schurExponentIdentificationKeptSeparate ≡ true
schurExponentIdentificationKeptSeparateIsTrue = refl
