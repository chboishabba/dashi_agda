{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopMachinHalfPhaseFromImaginaryProductExact where

------------------------------------------------------------------------
-- K05-PI: ACTUAL BISHOP MACHIN HALF-PHASE ON THE SOURCE ROUND11 SERIES.
--
-- Source owners already prove:
--  * 4*theta_M ~= pi_M, with original Machin atan series;
--  * exact algebraic sin(2theta) and cos(2theta) polynomials;
--  * one original imaginary Cauchy product derives the native
--    double-angle law and Pythagorean.
--
-- We compose these owners at theta_M. With precisely the two
-- independently owed analytic inputs (same original imaginary
-- Cauchy product and real quarter cosine=sine) we obtain:
--
--   sin_B(2theta_M) ~= 1, cos_B(2theta_M) ~= 0,
--   2*(2theta_M) ~= pi_M.
--
-- Crucially these are results for the actual existing Bishop
-- signed-factorial series, not a second symbolic sine/cosine.
-- No third Pythagorean or positive-quadrant assumption is added;
-- the unconditional strict quarter sine sign was independently
-- obtained in BishopMachinQuarterStrictSineFromTwoBallExact.
--
-- Machin; Bishop/Bridges; Murray/Csimma; original DASHI owners.
-- Source-written and --safe; independent Agda elaboration pending.
------------------------------------------------------------------------

import Real as R
import RealProperties as RP

import DASHI.Foundations.BishopMachinQuarterAngleBranchExact as Quarter
import DASHI.Analysis.BishopMachinQuarterPhaseQuadruplicationAlgebraExact as Quad
import DASHI.Analysis.BishopRound11ImaginaryProductPythagoreanReuseExact as Product
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

machinHalfPhase : R.ℝ
machinHalfPhase = Quad.twiceQuarter

doubleMachinHalfIsOriginalPi :
  R._≃_
    (R._+_ machinHalfPhase machinHalfPhase)
    (R._*_ (R._⋆ (Data.Rational.Unnormalised.+ 4 / 1)) Quarter.machinQuarterAngle)
doubleMachinHalfIsOriginalPi =
  Quad.twiceTwiceIsFourTimesQuarter

round11MachinHalfSineIsOne :
  (inputs : Round11.Round11BishopCutset) →
  (product : Product.Round11ImaginaryExpMultiplicative inputs) →
  R._≃_ (Quad.quarterCos inputs) (Quad.quarterSin inputs) →
  R._≃_ (Quad.round11Sine inputs machinHalfPhase) R.1ℝ
round11MachinHalfSineIsOne inputs product quarterEqual =
  RP.≃-trans
    (Quad.sineDouble
      (Product.round11DoubleAngleFromImaginaryProduct inputs product)
      Quarter.machinQuarterAngle)
    (Quad.sinDoubleIsOneAtEqualUnitPhase
      (Quad.quarterCos inputs)
      (Quad.quarterSin inputs)
      quarterEqual
      (Product.round11PythagoreanFromImaginaryProduct
        inputs product Quarter.machinQuarterAngle))

round11MachinHalfCosineIsZero :
  (inputs : Round11.Round11BishopCutset) →
  (product : Product.Round11ImaginaryExpMultiplicative inputs) →
  R._≃_ (Quad.quarterCos inputs) (Quad.quarterSin inputs) →
  R._≃_ (Quad.round11Cos inputs machinHalfPhase) R.0ℝ
round11MachinHalfCosineIsZero inputs product quarterEqual =
  RP.≃-trans
    (Quad.cosineDouble
      (Product.round11DoubleAngleFromImaginaryProduct inputs product)
      Quarter.machinQuarterAngle)
    (Quad.cosDoubleIsZeroAtEqualPhase
      (Quad.quarterCos inputs)
      (Quad.quarterSin inputs)
      quarterEqual)
