module DASHI.Analysis.BishopOriginalFiniteLogExpQuotientDefectSplitExact where

------------------------------------------------------------------------
-- K04d P0.03: EXACT ORIGINAL FINITE LOG-EXP QUOTIENT DEFECT SPLIT.
-- For literal F_N=exp_B(-L_N), P_N=L'_N, and q_E the original
-- error quotient, the exact defect is
--
--   q_E(N,x,h)-E'_N(x)
--    = -F_N(x) * [h*S_N(x,h)*Q(delta)
--                 +P_N(x)*(Q(delta)-1)].
--
-- S_N is the original finite log quotient's second-order factor.
-- delta is the actual negative finite log increment.
-- Q is the actual original shifted-factorial exponential quotient.
-- No limits, quotient division or assumed modulus.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Unnormalised using (1ℚᵘ)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopOriginalFiniteLogQuotientSecondOrderExact as Second
import DASHI.Analysis.BishopOriginalNegativeLogFiniteExplicitQuotientExact as Explicit
import DASHI.Analysis.BishopOriginalNegativeLogCrossWeightedIncrementExact as Cross
import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite
import DASHI.Analysis.BishopOriginalExpOriginDividedDifferenceSeriesExact as Origin
import DASHI.Analysis.BishopOriginalExpOriginDerivativeClosedExact as ExpClosed
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopLogAtanFiniteDerivativeGeometricExact as Geometric

sourceOriginalNegativeLogDelta :
  (stage : Nat) (x h : R.ℝ) → R.ℝ
sourceOriginalNegativeLogDelta =
  Explicit.originalSourceNegativeLogIncrement

sourceOriginalExpShiftedFactorial :
  (stage : Nat) (x h : R.ℝ) → R.ℝ
sourceOriginalExpShiftedFactorial stage x h =
  Origin.originalExpOriginQuotient
    (sourceOriginalNegativeLogDelta stage x h)

sourceOriginalPolynomialDefect :
  (stage : Nat) (x h : R.ℝ) → R.ℝ
sourceOriginalPolynomialDefect stage x h =
  Second.sourceFiniteLogSecondQuotient x h stage

sourceOriginalErrorSlopeDefect :
  (stage : Nat) (x h : R.ℝ) → R.ℝ
sourceOriginalErrorSlopeDefect stage x h =
  R._-_
    (Cross.sourceErrorQuotient stage x h)
    (Cross.sourceErrorSlope stage x)

originalFiniteLogErrorQuotientDefectSplit :
  (stage : Nat) (x h : R.ℝ) →
  let
    f = Finite.originalNegativeLogFiniteExponential x stage
    p = Geometric.negativeLogDerivativePolynomial x stage
    second = sourceOriginalPolynomialDefect stage x h
    q = sourceOriginalExpShiftedFactorial stage x h
  in
  R._≃_
    (sourceOriginalErrorSlopeDefect stage x h)
    (R._*_
      (R.-_ f)
      (R._+_
        (R._*_ (R._*_ h second) q)
        (R._*_ p (R._-_ q R.1ℝ))))
originalFiniteLogErrorQuotientDefectSplit stage x h =
  let
    f = Finite.originalNegativeLogFiniteExponential x stage
    p = Geometric.negativeLogDerivativePolynomial x stage
    second = sourceOriginalPolynomialDefect stage x h
    q = sourceOriginalExpShiftedFactorial stage x h
    logQ = Explicit.originalSourceFiniteLogQuotient stage x h
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (RP.+-cong
      (Explicit.originalFiniteLogErrorQuotientIsExplicit
        stage x h)
      RP.≃-refl)
    (RP.≃-trans
      (solve 4
        (λ ff qq pp logq →
          ((((⊝ Κ 1ℚᵘ) ⊗ logq) ⊗ (ff ⊗ qq))
            ⊕ Κ 1ℚᵘ)
            ⊖ ((ff ⊗ (⊝ pp)) ⊕ Κ 1ℚᵘ)
          ⊜ (⊝ ff) ⊗
              ((logq ⊗ qq) ⊖ pp))
        RP.≃-refl f q p logQ)
      (RP.*-cong
        RP.≃-refl
        (RP.≃-trans
          (RP.+-cong
            (RP.*-cong
              (Second.originalFiniteLogPolynomialQuotientExactDefect
                x h stage)
              RP.≃-refl)
            RP.≃-refl)
          (solve 4
            (λ hh ss pp qq →
              ((pp ⊕ (hh ⊗ ss)) ⊗ qq) ⊖ pp
              ⊜ ((hh ⊗ ss) ⊗ qq)
                ⊕ (pp ⊗ (qq ⊖ Κ 1ℚᵘ)))
            RP.≃-refl h second p q))))

-- Original P0.02 already supplies this bound, so consume it:
-- |Q(delta)-1| <= exp_B(|delta|)-1.
originalSourceShiftedFactorialErrorBound :
  (stage : Nat) (x h : R.ℝ) →
  R._≤_
    (R.∣ R._-_
      (sourceOriginalExpShiftedFactorial stage x h)
      R.1ℝ ∣)
    (R._-_
      (Exp.bishopExp
        (R.∣ sourceOriginalNegativeLogDelta stage x h ∣))
      R.1ℝ)
originalSourceShiftedFactorialErrorBound stage x h =
  ExpClosed.originalExpQuotientMinusOneAbsBound
    (sourceOriginalNegativeLogDelta stage x h)
