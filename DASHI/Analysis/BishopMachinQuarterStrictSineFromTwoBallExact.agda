{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopMachinQuarterStrictSineFromTwoBallExact where

------------------------------------------------------------------------
-- K05-PI: ACTUAL ROUND11 MACHIN QUARTER SINE STRICTLY POSITIVE.
--
-- This is an UNCONDITIONAL (relative only to the original Round11
-- configured Bishop input) constructive signed-factorial sign result,
-- not a fresh Pythagorean/atan/tan assumption.
--
-- Existing source owners provide:
--   3/4 < theta_M < 11/14  (BishopMachinQuarterAngleBranchExact)
--   87/128 <= sin_B(t) on 3/4 <= t <= 11/7, |t| <= 2
--      (BalabanBishopOuterBrillouinSineGapExact)
-- and the Round11 cutset constructs its signed-term identification.
--
-- Therefore: 0 < 87/128 <= sin_B(theta_M).
-- In particular, any remaining cos_B(theta_M)=sin_B(theta_M)
-- theorem has the strict positive quadrant branch available without
-- an extra analytic positivity assumption.
--
-- Bishop/Bridges; Murray/Csimma; Machin; Balaban;
-- original DASHI YM/quarter sign theorem owners.
-- Source-written; exact-head Agda kernel validation pending.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (0ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (toWitness)

import Real as R
import RealProperties as RP

import DASHI.Foundations.BishopMachinQuarterAngleBranchExact as Quarter
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11
import DASHI.Physics.YangMills.BalabanBishopSineTwoBallCubicLowerExact as TwoBall
import DASHI.Physics.YangMills.BalabanBishopOuterBrillouinSineGapExact as Outer
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary

quarterNonnegative :
  R.NonNegative Quarter.machinQuarterAngle
quarterNonnegative =
  RP.0≤x⇒nonNegx
    (RP.≤-trans
      (RP.<⇒≤
        (RP.p<q⇒p⋆<q⋆
          0ℚᵘ (+ 3 / 4)
          (toWitness
            {a? = QP._<?_ 0ℚᵘ (+ 3 / 4)} _)))
      (RP.<⇒≤ Quarter.threeFourthsBelowQuarter))

quarterBelowOuterUpper :
  R._≤_ Quarter.machinQuarterAngle (Outer.embed Outer.upperAngle)
quarterBelowOuterUpper =
  RP.≤-trans
    (RP.<⇒≤ Quarter.quarterBelowElevenFourteenths)
    (RP.<⇒≤
      (RP.p<q⇒p⋆<q⋆
        (+ 11 / 14) Outer.upperAngle
        (toWitness
          {a? = QP._<?_ (+ 11 / 14) Outer.upperAngle} _)))

quarterBelowTwo :
  R._≤_ Quarter.machinQuarterAngle TwoBall.bishopTwo
quarterBelowTwo =
  RP.≤-trans
    (RP.<⇒≤ Quarter.quarterBelowElevenFourteenths)
    (RP.<⇒≤
      (RP.p<q⇒p⋆<q⋆
        (+ 11 / 14) TwoBall.two
        (toWitness
          {a? = QP._<?_ (+ 11 / 14) TwoBall.two} _)))

quarterInsideTwo :
  R._≤_ (R.∣_∣ Quarter.machinQuarterAngle) TwoBall.bishopTwo
quarterInsideTwo =
  RP.≤-respˡ-≃
    (RP.nonNegx⇒∣x∣≃x quarterNonnegative)
    quarterBelowTwo

quarterSignedSineInputs :
  (inputs : Round11.Round11BishopCutset) →
  TwoBall.ConcreteTwoBallSineInputs
    (Round11.elementarySeries inputs)
    Quarter.machinQuarterAngle
quarterSignedSineInputs inputs = record
  { TwoBall.ConcreteTwoBallSineInputs.termIdentification =
      Round11.round11ConcreteTermIdentification inputs
  ; TwoBall.ConcreteTwoBallSineInputs.valueNonnegative =
      quarterNonnegative
  ; TwoBall.ConcreteTwoBallSineInputs.insideTwo =
      quarterInsideTwo
  }

round11MachinQuarterSineAboveEightySevenOverOneTwentyEight :
  (inputs : Round11.Round11BishopCutset) →
  R._≤_
    (Outer.embed Outer.lowerSine)
    (Elementary.bishopSin
      (Round11.elementarySeries inputs) Quarter.machinQuarterAngle)
round11MachinQuarterSineAboveEightySevenOverOneTwentyEight inputs =
  Outer.sineAboveEightySevenOverOneTwentyEight
    (quarterSignedSineInputs inputs)
    (RP.<⇒≤ Quarter.threeFourthsBelowQuarter)
    quarterBelowOuterUpper

round11MachinQuarterSineStrictPositive :
  (inputs : Round11.Round11BishopCutset) →
  R._<_
    R.0ℝ
    (Elementary.bishopSin
      (Round11.elementarySeries inputs) Quarter.machinQuarterAngle)
round11MachinQuarterSineStrictPositive inputs =
  RP.<-≤-trans
    (RP.p<q⇒p⋆<q⋆
      0ℚᵘ Outer.lowerSine
      (toWitness
        {a? = QP._<?_ 0ℚᵘ Outer.lowerSine} _))
    (round11MachinQuarterSineAboveEightySevenOverOneTwentyEight inputs)
