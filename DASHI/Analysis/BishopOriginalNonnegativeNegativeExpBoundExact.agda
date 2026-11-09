module DASHI.Analysis.BishopOriginalNonnegativeNegativeExpBoundExact where

------------------------------------------------------------------------
-- K04d P0: ORIGINAL exp_B(-u) ON THE CLOSED NONNEGATIVE HALF-LINE.
--
-- For each u >= 0, original bishopExp(u) >= 1 > 0.
-- The original Cauchy product proves bishopExp(-u)=inv(bishopExp u).
-- Consequently 0< bishopExp(-u)<=1, also at u=0, without an
-- undecidable constructive split into u=0 or u>0.
--
-- Applying this to the literal nonnegative original finite LOG sum
-- establishes 0 < F_N(x) <= 1 for EVERY x>=0 and EVERY stage N.
-- This is the genuine zero-cell witness needed by P0.05.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Sum.Base using (inj₂)
import Real as R
import RealProperties as RP
import Inverse as Inv
import Sequence as Seq

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as ExpOrder
import DASHI.Foundations.BishopExponentialCauchyProductExact as Product
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as Positive
import DASHI.Foundations.BishopNegativeLogGeometricSourceConvergenceExact as Log
import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite

originalPositiveExpOfNonnegative :
  (u : R.ℝ) →
  R.NonNegative u →
  R._<_ R.0ℝ (Exp.bishopExp u)
originalPositiveExpOfNonnegative u uNN =
  RP.<-≤-trans
    Positive.onePositive
    (ExpOrder.bishopExpAtLeastOneOnNonnegative uNN)

originalNegativeExpEqualsOriginalPositiveInverse :
  (u : R.ℝ) →
  (uNN : R.NonNegative u) →
  R._≃_
    (Exp.bishopExp (R.-_ u))
    (Inv._⁻¹ (Exp.bishopExp u)
      (inj₂ (originalPositiveExpOfNonnegative u uNN)))
originalNegativeExpEqualsOriginalPositiveInverse u uNN =
  let
    positive = Exp.bishopExp u
    negative = Exp.bishopExp (R.-_ u)
  in
  Inv.⁻¹-unique
    negative positive
    (inj₂ (originalPositiveExpOfNonnegative u uNN))
    (RP.≃-trans
      (RP.*-comm negative positive)
      (Product.bishopExpTimesNegativeIsOne u))

originalNegativeExpPositiveForNonnegative :
  (u : R.ℝ) →
  (uNN : R.NonNegative u) →
  R._<_ R.0ℝ (Exp.bishopExp (R.-_ u))
originalNegativeExpPositiveForNonnegative u uNN =
  let
    p = originalPositiveExpOfNonnegative u uNN
    invPositive = Inv.0<x⇒0<x⁻¹ (inj₂ p) p
  in
  RP.<-respʳ-≃
    (RP.≃-symm
      (originalNegativeExpEqualsOriginalPositiveInverse u uNN))
    invPositive

originalNegativeExpAtMostOneForNonnegative :
  (u : R.ℝ) →
  (uNN : R.NonNegative u) →
  R._≤_ (Exp.bishopExp (R.-_ u)) R.1ℝ
originalNegativeExpAtMostOneForNonnegative u uNN =
  let
    negative = Exp.bishopExp (R.-_ u)
    positive = Exp.bishopExp u
    expLower = ExpOrder.bishopExpAtLeastOneOnNonnegative uNN
    negativeNN = RP.0≤x⇒nonNegx
      (RP.<⇒≤ (originalNegativeExpPositiveForNonnegative u uNN))
    raw = RP.*-monoˡ-≤-nonNeg expLower negativeNN
    leftEquivalent = RP.*-identityʳ negative
    rightEquivalent =
      RP.≃-trans
        (RP.*-comm negative positive)
        (Product.bishopExpTimesNegativeIsOne u)
  in
  RP.≤-respʳ-≃ rightEquivalent
    (RP.≤-respˡ-≃
      (RP.≃-symm leftEquivalent) raw)

originalFiniteLogNonnegative :
  (x : R.ℝ) →
  (xNN : R.NonNegative x) →
  (stage : Nat) →
  R.NonNegative (Finite.originalLogFinitePartial x stage)
originalFiniteLogNonnegative x xNN zero = RP.nonNeg0
originalFiniteLogNonnegative x xNN (suc n) =
  RP.nonNegx,y⇒nonNegx+y
    (originalFiniteLogNonnegative x xNN n)
    (Log.sourceNegativeLogTermNonnegative x xNN n)

originalFiniteNegativeLogExpAtMostOneNonnegative :
  (x : R.ℝ) →
  (xNN : R.NonNegative x) →
  (stage : Nat) →
  R._≤_
    (R.∣ Finite.originalNegativeLogFiniteExponential x stage ∣)
    R.1ℝ
originalFiniteNegativeLogExpAtMostOneNonnegative x xNN stage =
  let
    u = Finite.originalLogFinitePartial x stage
    uNN = originalFiniteLogNonnegative x xNN stage
    fNN = RP.0≤x⇒nonNegx
      (RP.<⇒≤
        (originalNegativeExpPositiveForNonnegative u uNN))
  in
  RP.≤-respˡ-≃
    (RP.nonNegx⇒∣x∣≃x fNN)
    (originalNegativeExpAtMostOneForNonnegative u uNN)
