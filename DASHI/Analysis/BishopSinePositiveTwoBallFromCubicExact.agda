{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopSinePositiveTwoBallFromCubicExact where

------------------------------------------------------------------------
-- K05-PI: STRICT POSITIVITY ON THE ACTUAL RADIUS-TWO BISHOP SINE.
--
-- The existing Balaban sine owner proves the signed-series cubic bound
--
--   t - t^3/6 <= sin_B(t)    for t >= 0 and |t| <= 2.
--
-- This file supplies the independent missing SIGN proof:
--   t^2 <= 4  =>  1 - t^2/6 >= 1/3 > 0;
-- hence 0 < t(1-t^2/6) <= sin_B(t) for 0<t, |t|<=2.
--
-- We work on the exact existing Bishop setoid real and the original
-- Round11 configured signed-factorial term identification. No
-- trigonometric, differentiability, Cauchy product, pi or atan
-- equality is assumed.
--
-- Source: Bishop/Bridges, Murray/Csimma; original DASHI
-- BalabanBishopSineTwoBallCubicLowerExact theorem owners.
-- Source-written, Agda kernel acceptance pending.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (0ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as QP

import Real as R
import RealProperties as RP

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as E
import DASHI.Physics.YangMills.BalabanBishopSineTwoBallCubicLowerExact as Two
import DASHI.Physics.YangMills.BalabanP33BishopTaylorPolynomialFormExact as Poly
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

square : R.ℝ → R.ℝ
square x = R._*_ x x

sineFactor : R.ℝ → R.ℝ
sineFactor x =
  R._-_ R.1ℝ
    (R._*_ Poly.bishopOneSixth (square x))

positiveOneThird :
  R._<_ R.0ℝ Two.bishopOneThird
positiveOneThird =
  RP.p<q⇒p⋆<q⋆
    0ℚᵘ Two.oneThird
    (QP.positive⁻¹ Two.oneThird)

squareBoundedByFour :
  (x : R.ℝ) →
  R.NonNegative x →
  R._≤_ (R.∣_∣ x) Two.bishopTwo →
  R._≤_ (square x) Two.bishopFour
squareBoundedByFour x xNN insideTwo =
  RP.≤-respʳ-≃
    Two.bishopTwoSquareEquivalentFour
    (RP.*-mono-≤ xNN xNN
      (RP.≤-respˡ-≃
        (RP.nonNegx⇒∣x∣≃x xNN) insideTwo)
      (RP.≤-respˡ-≃
        (RP.nonNegx⇒∣x∣≃x xNN) insideTwo))

oneThirdIsOneMinusFourSixths :
  R._≃_
    Two.bishopOneThird
    (R._-_ R.1ℝ
      (R._*_ Poly.bishopOneSixth Two.bishopFour))
oneThirdIsOneMinusFourSixths =
  let open RP.ℝ-Solver
  in solve 0
    (Κ (+ 1 / 3) ⊜
      (Κ (+ 1 / 1) ⊖ (Κ (+ 1 / 6) ⊗ Κ (+ 4 / 1))))
    RP.≃-refl

oneThirdBelowSineFactor :
  (x : R.ℝ) →
  R.NonNegative x →
  R._≤_ (R.∣_∣ x) Two.bishopTwo →
  R._≤_ Two.bishopOneThird (sineFactor x)
oneThirdBelowSineFactor x xNN insideTwo =
  RP.≤-respˡ-≃
    (RP.≃-symm oneThirdIsOneMinusFourSixths)
    (RP.≤-respʳ-≃
      (let open RP.ℝ-Solver
       in solve 1
         (λ s →
           (Κ (+ 1 / 1) ⊕
             (⊝ (Κ (+ 1 / 6) ⊗ s)))
            ⊜ (Κ (+ 1 / 1) ⊖
             (Κ (+ 1 / 6) ⊗ s)))
         RP.≃-refl (square x))
      (RP.+-monoʳ-≤ R.1ℝ
        (RP.neg-mono-≤
          (RP.*-monoˡ-≤-nonNeg
            (squareBoundedByFour x xNN insideTwo)
            Two.bishopOneSixthNonnegative))))

sineFactorPositive :
  (x : R.ℝ) →
  R.NonNegative x →
  R._≤_ (R.∣_∣ x) Two.bishopTwo →
  R.Positive (sineFactor x)
sineFactorPositive x xNN insideTwo =
  RP.0<x⇒posx
    (RP.<-≤-trans
      positiveOneThird
      (oneThirdBelowSineFactor x xNN insideTwo))

cubicSineLowerFactors :
  (x : R.ℝ) →
  R._≃_
    (R._-_ x (Poly.sineCubicTerm x))
    (R._*_ x (sineFactor x))
cubicSineLowerFactors x =
  let open RP.ℝ-Solver
  in solve 1
    (λ z →
      z ⊖ (Κ (+ 1 / 6) ⊗ ((z ⊗ z) ⊗ z))
      ⊜ z ⊗ (Κ (+ 1 / 1) ⊖
        (Κ (+ 1 / 6) ⊗ (z ⊗ z))))
    RP.≃-refl x

round11SinePositiveOnStrictTwoBall :
  (inputs : Round11.Round11BishopCutset) →
  (x : R.ℝ) →
  R._<_ R.0ℝ x →
  R._≤_ (R.∣_∣ x) Two.bishopTwo →
  R._<_ R.0ℝ (E.bishopSin (Round11.elementarySeries inputs) x)
round11SinePositiveOnStrictTwoBall inputs x xPos insideTwo =
  let
    xNN : R.NonNegative x
    xNN = RP.0≤x⇒nonNegx (RP.<⇒≤ xPos)

    sourceInputs :
      Two.ConcreteTwoBallSineInputs
        (Round11.elementarySeries inputs) x
    sourceInputs = record
      { Two.ConcreteTwoBallSineInputs.termIdentification =
          Round11.round11ConcreteTermIdentification inputs
      ; Two.ConcreteTwoBallSineInputs.valueNonnegative = xNN
      ; Two.ConcreteTwoBallSineInputs.insideTwo = insideTwo
      }

    cubicPositive :
      R.Positive (R._-_ x (Poly.sineCubicTerm x))
    cubicPositive =
      RP.pos-cong
        (RP.≃-symm (cubicSineLowerFactors x))
        (RP.posx,y⇒posx*y
          (RP.0<x⇒posx xPos)
          (sineFactorPositive x xNN insideTwo))
  in
  RP.<-≤-trans
    (RP.posx⇒0<x cubicPositive)
    (Two.sineCubicLowerTwoBall sourceInputs)
