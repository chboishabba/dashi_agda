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
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as PositiveUnit
open import Data.Rational.Unnormalised using (1ℚᵘ)

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

------------------------------------------------------------------------
-- Uniform control of the original *whole quotient*, not only its
-- first-order defect:
--
-- |Q(u)| <= exp_B(rho)  whenever |u|<=rho and rho>=0.
--
-- This is obtained by the literal identity Q=(Q-1)+1 and the
-- already established source |Q-1| bound; no additional series.
------------------------------------------------------------------------

originalShiftedFactorialAbsoluteBelowExpBall :
  (radius : R.ℝ) →
  (radiusNN : R.NonNegative radius) →
  (u : R.ℝ) →
  R._≤_ (R.∣ u ∣) radius →
  R._≤_
    (R.∣ Origin.originalExpOriginQuotient u ∣)
    (Exp.bishopExp radius)
originalShiftedFactorialAbsoluteBelowExpBall
    radius radiusNN u inside =
  let
    q = Origin.originalExpOriginQuotient u
    e = Exp.bishopExp radius
    oneNN = RP.0≤x⇒nonNegx
      (RP.<⇒≤ PositiveUnit.onePositive)
    open RP.ℝ-Solver
    splitQ =
      solve 1
        (λ qq →
          qq ⊜ (qq ⊖ Κ 1ℚᵘ) ⊕ Κ 1ℚᵘ)
        RP.≃-refl q
    upper =
      RP.≤-trans
        (RP.∣x+y∣≤∣x∣+∣y∣
          (R._-_ q R.1ℝ) R.1ℝ)
        (RP.+-mono-≤
          (originalShiftedFactorialExpQuotientUniformModulus
            radius radiusNN u inside)
          RP.≤-refl)
    target =
      RP.≃-trans
        (RP.+-cong
          RP.≃-refl
          (RP.nonNegx⇒∣x∣≃x oneNN))
        (solve 1
          (λ ee →
            (ee ⊖ Κ 1ℚᵘ) ⊕ Κ 1ℚᵘ ⊜ ee)
          RP.≃-refl e)
  in
  RP.≤-respˡ-≃
    (RP.∣-∣-cong splitQ)
    (RP.≤-respʳ-≃ target upper)
