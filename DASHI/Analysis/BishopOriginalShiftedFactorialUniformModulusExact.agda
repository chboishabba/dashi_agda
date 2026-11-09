module DASHI.Analysis.BishopOriginalShiftedFactorialUniformModulusExact where

------------------------------------------------------------------------
-- K04d P0.02: SOURCE SHIFTED-FACTORIAL EXP QUOTIENT UNIFORM MODULUS.
--
-- For the original literal Q(u)=sum_{k>=0} u^k/(k+1)!,
-- existing originalExpQuotientMinusOneAbsBound establishes:
--   |Q(u)-1| <= exp_B(|u|)-1.
--
-- Existing bishopExpMonotoneNonnegative upgrades it, for every
-- genuine Bishop radius rho>=0, to the COMMON uniform inequality
--
--   |u| <= rho  ==>  |Q(u)-1| <= exp_B(rho)-1.
--
-- This proves the *uniform in u* P0.02 source majorant rather
-- than merely pointwise convergence. It requires no selected
-- synthetic exp or generic continuity axiom.
--
-- For a mesh-size modulus, still need |delta_N(x,h)| <= rho(h)
-- with rho(h)->0 uniformly in the compact source interval.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import DASHI.Analysis.BishopOriginalNegativeLogFiniteExplicitQuotientExact as Explicit
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopOriginalExpOriginDividedDifferenceSeriesExact as Origin
import DASHI.Analysis.BishopOriginalExpOriginDerivativeClosedExact as ExpClosed
import DASHI.Foundations.BishopExponentialNonnegativeMonotoneExact as ExpMono
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp

originalShiftedFactorialExpQuotientUniformModulus :
  (radius : R.ℝ) →
  (radiusNonnegative : R.NonNegative radius) →
  (u : R.ℝ) →
  R._≤_ (R.∣ u ∣) radius →
  R._≤_
    (R.∣ R._-_
      (Origin.originalExpOriginQuotient u)
      R.1ℝ ∣)
    (R._-_
      (Exp.bishopExp radius)
      R.1ℝ)
originalShiftedFactorialExpQuotientUniformModulus
    radius radiusNonnegative u uInside =
  RP.≤-trans
    (ExpClosed.originalExpQuotientMinusOneAbsBound u)
    (RP.+-mono-≤
      (ExpMono.bishopExpMonotoneNonnegative
        (RP.nonNeg∣x∣ u)
        uInside)
      RP.≤-refl)

-- Direct original LOG-EXP same-source specialization:
-- the argument is the actual negative finite-log increment.
originalNegativeLogShiftedFactorialUniformModulus :
  (stage : Nat) →
  (x h radius : R.ℝ) →
  (radiusNonnegative : R.NonNegative radius) →
  R._≤_
    (R.∣
      Explicit.originalSourceNegativeLogIncrement
        stage x h ∣)
    radius →
  R._≤_
    (R.∣ R._-_
      (Origin.originalExpOriginQuotient
        (Explicit.originalSourceNegativeLogIncrement
          stage x h))
      R.1ℝ ∣)
    (R._-_ (Exp.bishopExp radius) R.1ℝ)
originalNegativeLogShiftedFactorialUniformModulus
    stage x h radius radiusNonnegative deltaInside =
  originalShiftedFactorialExpQuotientUniformModulus
    radius radiusNonnegative
    (Explicit.originalSourceNegativeLogIncrement
      stage x h)
    deltaInside
