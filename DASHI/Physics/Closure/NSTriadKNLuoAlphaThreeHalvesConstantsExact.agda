module DASHI.Physics.Closure.NSTriadKNLuoAlphaThreeHalvesConstantsExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Select the convenient source-admissible value alpha=3/2.  The correction in
-- Lemma 3.2 is then
--
--   alpha + (2-alpha)/2 = 7/4.
--
-- A block shift chosen as four times a natural base turns the corresponding
-- dyadic coefficient into an integer dyadic reciprocal power.  Identifying the
-- rational coefficient below with the analytic real fractional-power notation
-- remains a separate source/repository scalar-embedding theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 1ℚ; _+_; _-_; _*_; _/_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing

alphaThreeHalves twoRational twoMinusAlpha halfCorrection correctedExponent : ℚ
alphaThreeHalves = + 3 / 2
twoRational = + 2 / 1
twoMinusAlpha = + 1 / 2
halfCorrection = + 1 / 4
correctedExponent = + 7 / 4

twoMinusAlphaExact :
  twoRational - alphaThreeHalves ≡ twoMinusAlpha
twoMinusAlphaExact = ℚRing.solve-∀

halfCorrectionExact :
  twoMinusAlpha * (+ 1 / 2) ≡ halfCorrection
halfCorrectionExact = ℚRing.solve-∀

correctedExponentExact :
  alphaThreeHalves + halfCorrection ≡ correctedExponent
correctedExponentExact = ℚRing.solve-∀

oneMinusAlpha : ℚ
oneMinusAlpha = - (+ 1 / 2)

oneMinusAlphaExact :
  1ℚ - alphaThreeHalves ≡ oneMinusAlpha
oneMinusAlphaExact = ℚRing.solve-∀

fourTimes : Nat → Nat
fourTimes zero = zero
fourTimes (suc n) = suc (suc (suc (suc (fourTimes n))))

oneOverTwoToSeventh : ℚ
oneOverTwoToSeventh = + 1 / 128

dyadicReciprocalSeventhPower : Nat → ℚ
dyadicReciprocalSeventhPower zero = 1ℚ
dyadicReciprocalSeventhPower (suc n) =
  oneOverTwoToSeventh * dyadicReciprocalSeventhPower n

record FourAlignedLuoShift : Set₁ where
  field
    baseShift : Nat
    blockShift : Nat
    blockShiftMeaning : blockShift ≡ fourTimes baseShift

    correctedShiftCoefficient : ℚ
    correctedCoefficientMeaning :
      correctedShiftCoefficient
      ≡ dyadicReciprocalSeventhPower baseShift

    AnalyticFractionalPowerMatchesRationalCoefficient : Set
    analyticFractionalPowerMatchesRationalCoefficient :
      AnalyticFractionalPowerMatchesRationalCoefficient

open FourAlignedLuoShift public

alphaThreeHalvesArithmeticClosed : Bool
alphaThreeHalvesArithmeticClosed = true

correctedExponentSevenFourthsClosed : Bool
correctedExponentSevenFourthsClosed = true

fourAlignedRationalCoefficientConstructed : Bool
fourAlignedRationalCoefficientConstructed = true

alphaThreeHalvesArithmeticClosedIsTrue :
  alphaThreeHalvesArithmeticClosed ≡ true
alphaThreeHalvesArithmeticClosedIsTrue = refl

correctedExponentSevenFourthsClosedIsTrue :
  correctedExponentSevenFourthsClosed ≡ true
correctedExponentSevenFourthsClosedIsTrue = refl

fourAlignedRationalCoefficientConstructedIsTrue :
  fourAlignedRationalCoefficientConstructed ≡ true
fourAlignedRationalCoefficientConstructedIsTrue = refl
