{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalNegativeLogFiniteExpUniformResidualExact where

------------------------------------------------------------------------
-- P0: UNIFORM, EXPLICIT ORIGINAL FINITE EXP-LOG RESIDUAL MAJORANT.
--
-- The exact previously proved factor-derivative residual is
--  (1-x) F_N'(x) + F_N(x) ~= x^N F_N(x),
-- where F_N = original exp_B(-sourceNegativeLogPartial_N).
--
-- This owner proves on EVERY source compact 0<x<=r<1:
--        |x^N F_N(x)| <= r^N       (N >= 1).
--
-- Crucial genuine inputs already proved on the original carrier:
--  * sourceNegativeLogTermNonnegative and monotone finite sums;
--  * sourceLogFirstPartialEqualsX;
--  * negativeExpPositive and negativeExpBelowOne;
--  * original x<=r -> x^N<=r^N;
--  * nonnegative product absolute normalization.
--
-- The cutoff r^N -> 0 is independent of x: this is the actual
-- uniform ODE residual, not just pointwise coefficient convergence.
--
-- This does not postulate FTC, integration, global ODE uniqueness,
-- nor identify exp(-L)=1-x merely from small residuals.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Foundations.BishopNegativeLogGeometricSourceConvergenceExact as Log
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as NegativeExp
import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite

-- The literal first nonzero term is exactly x; all later signed-log
-- coefficients are nonnegative on the original positive source.
originalLogFinitePartialAtLeastPoint :
  (x : R.ℝ) →
  (xNonnegative : R.NonNegative x) →
  (n : Nat) →
  R._≤_ x
    (Finite.originalLogFinitePartial x (suc n))
originalLogFinitePartialAtLeastPoint x xNonnegative zero =
  RP.≤-reflexive
    (RP.≃-symm (Log.sourceLogFirstPartialEqualsX x))
originalLogFinitePartialAtLeastPoint x xNonnegative (suc n) =
  RP.≤-trans
    (originalLogFinitePartialAtLeastPoint x xNonnegative n)
    (Log.sourceLogPartialIncreasing x xNonnegative (suc n))

originalLogFinitePartialStrictlyPositive :
  (x : R.ℝ) →
  (xPositive : R._<_ R.0ℝ x) →
  (n : Nat) →
  R._<_ R.0ℝ
    (Finite.originalLogFinitePartial x (suc n))
originalLogFinitePartialStrictlyPositive x xPositive n =
  RP.<-≤-trans
    xPositive
    (originalLogFinitePartialAtLeastPoint
      x (RP.0≤x⇒nonNegx (RP.<⇒≤ xPositive)) n)

-- Original bounded positive exp factor at every finite positive
-- source partial: no monotonic-exp shortcut at an unselected value.
originalFiniteNegativeLogExpPositive :
  (x : R.ℝ) →
  (xPositive : R._<_ R.0ℝ x) →
  (n : Nat) →
  R._<_ R.0ℝ
    (Finite.originalNegativeLogFiniteExponential x (suc n))
originalFiniteNegativeLogExpPositive x xPositive n =
  NegativeExp.negativeExpPositive
    (originalLogFinitePartialStrictlyPositive x xPositive n)

originalFiniteNegativeLogExpBelowOne :
  (x : R.ℝ) →
  (xPositive : R._<_ R.0ℝ x) →
  (n : Nat) →
  R._<_
    (Finite.originalNegativeLogFiniteExponential x (suc n))
    R.1ℝ
originalFiniteNegativeLogExpBelowOne x xPositive n =
  NegativeExp.negativeExpBelowOne
    (originalLogFinitePartialStrictlyPositive x xPositive n)

-- Signed residual x^N F_N is nonnegative for source x>0.
originalFiniteNegativeLogExpResidualNonnegative :
  (x : R.ℝ) →
  (xPositive : R._<_ R.0ℝ x) →
  (n : Nat) →
  R.NonNegative
    (R._*_
      (Finite.originalNegativeLogFiniteExponential x (suc n))
      (R.pow x (suc n)))
originalFiniteNegativeLogExpResidualNonnegative x xPositive n =
  RP.nonNegx,y⇒nonNegx*y
    (RP.0≤x⇒nonNegx
      (RP.<⇒≤ (originalFiniteNegativeLogExpPositive x xPositive n)))
    (Seq.nonNegx⇒nonNegxⁿ (suc n)
      (RP.0≤x⇒nonNegx (RP.<⇒≤ xPositive)))

-- The bound is UNIFORM in x: its only analytic scale is the
-- actual original Bishop power r^N, for one chosen 0<r<1.
originalFiniteNegativeLogExpUniformResidualBound :
  (radius x : R.ℝ) →
  (xPositive : R._<_ R.0ℝ x) →
  (xInside : R._≤_ x radius) →
  (n : Nat) →
  R._≤_
    (R.∣ R._*_
      (Finite.originalNegativeLogFiniteExponential x (suc n))
      (R.pow x (suc n)) ∣)
    (R.pow radius (suc n))
originalFiniteNegativeLogExpUniformResidualBound
    radius x xPositive xInside n =
  let
    powNonnegative =
      Seq.nonNegx⇒nonNegxⁿ
        (suc n) (RP.0≤x⇒nonNegx (RP.<⇒≤ xPositive))
    expBelow =
      RP.<⇒≤ (originalFiniteNegativeLogExpBelowOne x xPositive n)
    boundExpByOne =
      RP.≤-respʳ-≃
        (RP.*-identityˡ (R.pow x (suc n)))
        (RP.*-monoʳ-≤-nonNeg
          expBelow powNonnegative)
    boundPower =
      Seq.x≤y∧nonNegx⇒xⁿ≤yⁿ
        (suc n) xInside
        (RP.0≤x⇒nonNegx (RP.<⇒≤ xPositive))
  in
  RP.≤-respˡ-≃
    (RP.nonNegx⇒∣x∣≃x
      (originalFiniteNegativeLogExpResidualNonnegative
        x xPositive n))
    (RP.≤-trans boundExpByOne boundPower)
