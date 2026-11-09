module DASHI.Analysis.BishopOriginalFiniteLogExpStagewiseUniformDefectExact where

------------------------------------------------------------------------
-- K04d P0.03: FULL FIXED-STAGE ORIGINAL BISHOP QUOTIENT MODULUS.
--
-- For every fixed finite stage N=suc n and positive original x,
-- with 0<x<=r and 0<=x+h<=r, set:
--
-- P = negativeLogDerivativePolynomial r N
-- S = sourceFiniteLogSecondQuotient r 0 N
-- rho = |h|*P
-- B = (|h|*S)*exp_B(rho) + P*(exp_B(rho)-1).
--
-- Then the literal original error quotient obeys
--
--       |q_E(N,x,h) - E'_N(x)| <= B.
--
-- This is UNIFORM in x and the sign of h at fixed N/r. Its right
-- side tends to zero as h->0, by the previously source-proved
-- continuity exp_B and the native nonnegative coefficient facts.
--
-- This does NOT assert uniformity over all N or a continuous
-- endpoint comparison; these are separate P0.06 obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopOriginalFiniteLogQuotientUniformModulusExact as UniformLog
import DASHI.Analysis.BishopOriginalFiniteLogSecondQuotientPositiveExact as PositiveLog
import DASHI.Analysis.BishopOriginalFiniteLogQuotientRadiusDominanceExact as Radius
import DASHI.Analysis.BishopOriginalFiniteLogExpQuotientTriangleExact as Triangle
import DASHI.Analysis.BishopOriginalFiniteLogExpQuotientDefectSplitExact as Split
import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite
import DASHI.Analysis.BishopOriginalNegativeLogFiniteExpUniformResidualExact as FiniteExpOrder
import DASHI.Analysis.BishopOriginalFiniteLogQuotientSecondOrderExact as Second
import DASHI.Analysis.BishopOriginalShiftedFactorialUniformModulusExact as Shift
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as ExpOrder
import DASHI.Foundations.BishopLogAtanFiniteDerivativeGeometricExact as Geo
import Sequence as Seq
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as PositiveUnit

sourceOriginalUniformErrorBudget :
  (n : Nat) (radius h : R.ℝ) → R.ℝ
sourceOriginalUniformErrorBudget n radius h =
  let
    p = Geo.negativeLogDerivativePolynomial radius n
    s = Second.sourceFiniteLogSecondQuotient radius R.0ℝ n
    rho = R._*_ (R.∣ h ∣) p
    expRho = Exp.bishopExp rho
  in
  R._+_
    (R._*_ (R._*_ (R.∣ h ∣) s) expRho)
    (R._*_ p (R._-_ expRho R.1ℝ))

sourceOriginalUniformErrorBudgetNonnegative :
  (n : Nat) (radius h : R.ℝ) →
  (radiusNN : R.NonNegative radius) →
  R.NonNegative (sourceOriginalUniformErrorBudget n radius h)
sourceOriginalUniformErrorBudgetNonnegative n radius h radiusNN =
  let
    p = Geo.negativeLogDerivativePolynomial radius n
    s = Second.sourceFiniteLogSecondQuotient radius R.0ℝ n
    rho = R._*_ (R.∣ h ∣) p
    expRho = Exp.bishopExp rho
    pNN = Radius.originalFiniteLogRadiusDerivativeNonnegative
      radius radiusNN n
    radiusPlusZeroNN = RP.nonNeg-cong
      (RP.≃-symm (RP.+-identityʳ radius)) radiusNN
    sNN = PositiveLog.originalFiniteLogSecondQuotientNonnegative
      radius R.0ℝ radiusNN radiusPlusZeroNN n
    rhoNN = RP.nonNegx,y⇒nonNegx*y (RP.nonNeg∣x∣ h) pNN
    expLower = ExpOrder.bishopExpAtLeastOneOnNonnegative rhoNN
    expNN = RP.0≤x⇒nonNegx
      (RP.≤-trans
        (RP.nonNegx⇒0≤x
          (RP.0≤x⇒nonNegx
            (RP.<⇒≤
              PositiveUnit.onePositive)))
        expLower)
    expMinusOneNN = RP.0≤x⇒nonNegx
      (Seq.x≤y⇒0≤y-x expLower)
  in
  RP.nonNegx,y⇒nonNegx+y
    (RP.nonNegx,y⇒nonNegx*y
      (RP.nonNegx,y⇒nonNegx*y (RP.nonNeg∣x∣ h) sNN)
      expNN)
    (RP.nonNegx,y⇒nonNegx*y pNN expMinusOneNN)

originalFiniteLogExpStagewiseUniformDefectWithFactor :
  (n : Nat) (radius x h : R.ℝ) →
  (xNN : R.NonNegative x) →
  (yNN : R.NonNegative (R._+_ x h)) →
  (xInside : R._≤_ x radius) →
  (yInside : R._≤_ (R._+_ x h) radius) →
  R._≤_
    (R.∣ Split.sourceOriginalErrorSlopeDefect n x h ∣)
    (R._*_
      (R.∣ Finite.originalNegativeLogFiniteExponential x n ∣)
      (sourceOriginalUniformErrorBudget n radius h))
originalFiniteLogExpStagewiseUniformDefectWithFactor
    n radius x h xNN yNN xInside yInside =
  let
    p = Geo.negativeLogDerivativePolynomial radius n
    s = Second.sourceFiniteLogSecondQuotient radius R.0ℝ n
    q = Split.sourceOriginalExpShiftedFactorial n x h
    rho = R._*_ (R.∣ h ∣) p
    e = Exp.bishopExp rho
    radiusNN = UniformLog.sourceRadiusNonnegative
      x radius xNN xInside
    pNN = Radius.originalFiniteLogRadiusDerivativeNonnegative
      radius radiusNN n
    rPlusZeroNN = RP.nonNeg-cong
      (RP.≃-symm (RP.+-identityʳ radius)) radiusNN
    sNN = PositiveLog.originalFiniteLogSecondQuotientNonnegative
      radius R.0ℝ radiusNN rPlusZeroNN n
    rhoNN = RP.nonNegx,y⇒nonNegx*y
      (RP.nonNeg∣x∣ h) pNN
    delta = Split.sourceOriginalNegativeLogDelta n x h
    deltaInside =
      Radius.originalNegativeLogIncrementUniformRadiusBound
        n radius x h xNN yNN xInside yInside
    qBound =
      Shift.originalShiftedFactorialAbsoluteBelowExpBall
        rho rhoNN delta deltaInside
    qDefectBound =
      Shift.originalShiftedFactorialExpQuotientUniformModulus
        rho rhoNN delta deltaInside
    first =
      RP.*-monoʳ-≤-nonNeg
        qBound
        (RP.nonNegx,y⇒nonNegx*y
          (RP.nonNeg∣x∣ h) sNN)
    second = RP.*-monoˡ-≤-nonNeg qDefectBound pNN
  in
  RP.≤-trans
    (Triangle.originalFiniteLogErrorQuotientRadiusTriangle
      n radius x h xNN yNN xInside yInside)
    (RP.*-monoˡ-≤-nonNeg
      (RP.+-mono-≤ first second)
      (RP.nonNeg∣x∣
        (Finite.originalNegativeLogFiniteExponential x n)))

originalFiniteLogErrorQuotientUniformModulus :
  (n : Nat) (radius x h : R.ℝ) →
  (xPositive : R._<_ R.0ℝ x) →
  (yNN : R.NonNegative (R._+_ x h)) →
  (xInside : R._≤_ x radius) →
  (yInside : R._≤_ (R._+_ x h) radius) →
  R._≤_
    (R.∣ Split.sourceOriginalErrorSlopeDefect (suc n) x h ∣)
    (sourceOriginalUniformErrorBudget (suc n) radius h)
originalFiniteLogErrorQuotientUniformModulus
    n radius x h xPositive yNN xInside yInside =
  let
    f = Finite.originalNegativeLogFiniteExponential x (suc n)
    budget = sourceOriginalUniformErrorBudget (suc n) radius h
    radiusNN = UniformLog.sourceRadiusNonnegative
      x radius (RP.0≤x⇒nonNegx (RP.<⇒≤ xPositive)) xInside
    fAbsBelowOne =
      RP.≤-respˡ-≃
        (RP.nonNegx⇒∣x∣≃x
          (RP.0≤x⇒nonNegx
            (RP.<⇒≤
              (FiniteExpOrder.originalFiniteNegativeLogExpPositive
                x xPositive n))))
        (RP.<⇒≤
          (FiniteExpOrder.originalFiniteNegativeLogExpBelowOne
            x xPositive n))
  in
  RP.≤-trans
    (originalFiniteLogExpStagewiseUniformDefectWithFactor
      (suc n) radius x h
      (RP.0≤x⇒nonNegx (RP.<⇒≤ xPositive))
      yNN xInside yInside)
    (RP.≤-respʳ-≃
      (RP.*-identityˡ budget)
      (RP.*-monoʳ-≤-nonNeg
        fAbsBelowOne
        (sourceOriginalUniformErrorBudgetNonnegative
          (suc n) radius h radiusNN)))
