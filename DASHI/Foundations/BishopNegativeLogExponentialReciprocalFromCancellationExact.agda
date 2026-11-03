{-# OPTIONS --safe #-}
module DASHI.Foundations.BishopNegativeLogExponentialReciprocalFromCancellationExact where

------------------------------------------------------------------------
-- K04d-LOG: NATIVE BISHOP RECIPROCAL FROM THE ORIGINAL LOG SERIES.
--
-- Reuse:
--  * the real native exp(x)*exp(-x) ≃ 1 Cauchy theorem;
--  * the *actual* original convergent source log sum L(x);
--  * the one-minus-unit-interval positive/nonzero witness;
--  * the exact Bishop inverse-uniqueness theorem.
--
-- It suffices now to prove exp_B(-L(x)) ≃ 1-x at the actual
-- canonical coefficients, instead of independently proving the
-- harder exp_B(L(x)) ≃ (1-x)^(-1) and its inverse cancellation.
--
-- This theorem is a genuine setoid proof REDUCTION, not an
-- unconditional exp/log inverse. The negative-exponential
-- series identity is still a separate mathematical proof gate.
--
-- Bishop & Bridges; Zachary Murray (2022); Viktor Csimma;
-- original DASHI finite geometric / exponential authors.
-- Source-written; kernel elaboration pending.
------------------------------------------------------------------------

import Real as R
import RealProperties as RP
import DASHI.Foundations.BishopNegativeLogGeometricSourceConvergenceExact as Log
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialCauchyProductExact as Product
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as Identity
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Geometric
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal
import DASHI.Foundations.BishopInverseSquareProductExact as Inverse

open Geometric.BishopUnitIntervalRatio

sourceOneMinusRatio :
  (x : R.ℝ) →
  R._<_ R.0ℝ x →
  R._<_ x R.1ℝ →
  Geometric.BishopUnitIntervalRatio x
sourceOneMinusRatio x positive belowOne = record
  { ratioNonnegative = RP.<⇒≤ positive
  ; ratioBelowOne = belowOne
  }

sourceNegativeLogValue :
  (x : R.ℝ) →
  (positive : R._<_ R.0ℝ x) →
  (belowOne : R._<_ x R.1ℝ) →
  R.ℝ
sourceNegativeLogValue x positive belowOne =
  Log.sourceNegativeLogValue x positive belowOne

negativeLogExpAndMinusExpCancel :
  (x : R.ℝ) →
  (positive : R._<_ R.0ℝ x) →
  (belowOne : R._<_ x R.1ℝ) →
  R._≃_
    (R._*_
      (Exp.bishopExp (sourceNegativeLogValue x positive belowOne))
      (Exp.bishopExp (R.-_ (sourceNegativeLogValue x positive belowOne))))
    R.1ℝ
negativeLogExpAndMinusExpCancel x positive belowOne =
  Product.bishopExpTimesNegativeIsOne
    (sourceNegativeLogValue x positive belowOne)

negativeLogExpCancelsOneMinus :
  (x : R.ℝ) →
  (positive : R._<_ R.0ℝ x) →
  (belowOne : R._<_ x R.1ℝ) →
  R._≃_
    (Exp.bishopExp
      (R.-_ (sourceNegativeLogValue x positive belowOne)))
    (Identity.oneMinus x) →
  R._≃_
    (R._*_
      (Exp.bishopExp (sourceNegativeLogValue x positive belowOne))
      (Identity.oneMinus x))
    R.1ℝ
negativeLogExpCancelsOneMinus x positive belowOne negativeExpIsGap =
  RP.≃-trans
    (RP.*-cong RP.≃-refl (RP.≃-symm negativeExpIsGap))
    (negativeLogExpAndMinusExpCancel x positive belowOne)

negativeLogExpIsActualBishopInverse :
  (x : R.ℝ) →
  (positive : R._<_ R.0ℝ x) →
  (belowOne : R._<_ x R.1ℝ) →
  R._≃_
    (Exp.bishopExp
      (R.-_ (sourceNegativeLogValue x positive belowOne)))
    (Identity.oneMinus x) →
  R._≃_
    (Exp.bishopExp (sourceNegativeLogValue x positive belowOne))
    (Inverse.inverse
      (Identity.oneMinus x)
      (Reciprocal.gapNonzero
        (sourceOneMinusRatio x positive belowOne)))
negativeLogExpIsActualBishopInverse x positive belowOne identity =
  RP.≃-symm
    (Inverse.inverseFromCancellation
      (Identity.oneMinus x)
      (Exp.bishopExp (sourceNegativeLogValue x positive belowOne))
      (Reciprocal.gapNonzero
        (sourceOneMinusRatio x positive belowOne))
      (negativeLogExpCancelsOneMinus
        x positive belowOne identity))
