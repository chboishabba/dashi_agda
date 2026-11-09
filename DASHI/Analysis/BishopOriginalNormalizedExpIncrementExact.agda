module DASHI.Analysis.BishopOriginalNormalizedExpIncrementExact where

------------------------------------------------------------------------
-- K04d P0.05: ORIGINAL NORMALIZED EXPONENTIAL LOCAL INCREMENT.
--
-- On the actual pinned Bishop real and with genuine 0<=x<1
-- witnesses, let G_N(x)=F_N(x)*(1-x)^(-1), F_N=exp_B(-L_N).
-- Then without division by h:
--
--   (1-a)(1-b) [G_N(b)-G_N(a)]
--     = (1-a)F_N(b) - (1-b)F_N(a).
--
-- At b=a+h, the original local ODE gives
--
--   (1-a)(1-b) [G_N(b)-G_N(a)]
--     = h * [a^N F_N(a) + (1-a)(q_E(a,h)-E'_N(a))].
--
-- Both are exact same-source identities with a *positive* local
-- denominator. This avoids dividing by a product of all mesh
-- weights, which can degenerate as the mesh is refined.
--
-- No integrated endpoint inequality or uniform quotient modulus
-- is claimed by this file. Exact-head Agda kernel check pending.
--
-- Source: Bishop/Bridges, pinned Murray/Csimma Real and Inverse,
-- DASHI finite original log exp and cross-weight ODE.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Unnormalised using (1ℚᵘ)
import Real as R
import RealProperties as RP
import Inverse as Inv

import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite
import DASHI.Analysis.BishopOriginalNegativeLogCrossWeightedIncrementExact as Cross
import DASHI.Analysis.BishopOriginalNegativeLogCrossWeightCocycleExact as Cocycle
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Gap

originalNormalizedFiniteExp :
  (stage : Nat) (x : R.ℝ) →
  Gap.BishopUnitIntervalRatio x → R.ℝ
originalNormalizedFiniteExp stage x inside =
  R._*_
    (Finite.originalNegativeLogFiniteExponential x stage)
    (Gap.oneMinusInverse inside)

originalNormalizedFiniteExpCross :
  (stage : Nat) (a b : R.ℝ) →
  (aInside : Gap.BishopUnitIntervalRatio a) →
  (bInside : Gap.BishopUnitIntervalRatio b) → R.ℝ
originalNormalizedFiniteExpCross stage a b aInside bInside =
  R._*_
    (R._*_ (Cross.oneMinus a) (Cross.oneMinus b))
    (R._-_
      (originalNormalizedFiniteExp stage b bInside)
      (originalNormalizedFiniteExp stage a aInside))

originalNormalizedFiniteExpCrossIsSourceCross :
  (stage : Nat) (a b : R.ℝ) →
  (aInside : Gap.BishopUnitIntervalRatio a) →
  (bInside : Gap.BishopUnitIntervalRatio b) →
  R._≃_
    (originalNormalizedFiniteExpCross
      stage a b aInside bInside)
    (Cocycle.sourceCrossAt stage a b)
originalNormalizedFiniteExpCrossIsSourceCross
    stage a b aInside bInside =
  let
    wa = Cross.oneMinus a
    wb = Cross.oneMinus b
    fa = Finite.originalNegativeLogFiniteExponential a stage
    fb = Finite.originalNegativeLogFiniteExponential b stage
    ia = Gap.oneMinusInverse aInside
    ib = Gap.oneMinusInverse bInside
    cancelA = Inv.*-inverseˡ wa (Gap.oneMinusNonzero aInside)
    cancelB = Inv.*-inverseˡ wb (Gap.oneMinusNonzero bInside)
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (solve 6
      (λ wa′ wb′ fa′ fb′ ia′ ib′ →
        (wa′ ⊗ wb′) ⊗
          ((fb′ ⊗ ib′) ⊖ (fa′ ⊗ ia′))
        ⊜
          ((wa′ ⊗ fb′) ⊗ (ib′ ⊗ wb′))
          ⊖ ((wb′ ⊗ fa′) ⊗ (ia′ ⊗ wa′)))
      RP.≃-refl wa wb fa fb ia ib)
    (RP.≃-trans
      (RP.+-cong
        (RP.*-cong RP.≃-refl cancelB)
        (RP.-‿cong
          (RP.*-cong RP.≃-refl cancelA)))
      (solve 4
        (λ wa′ wb′ fa′ fb′ →
          ((wa′ ⊗ fb′) ⊗ Κ 1ℚᵘ)
          ⊖ ((wb′ ⊗ fa′) ⊗ Κ 1ℚᵘ)
          ⊜ (wa′ ⊗ fb′) ⊖ (wb′ ⊗ fa′))
        RP.≃-refl wa wb fa fb))

originalNormalizedFiniteExpIncrementIsResidualPlusDefect :
  (stage : Nat) (x h : R.ℝ) →
  (xInside : Gap.BishopUnitIntervalRatio x) →
  (yInside : Gap.BishopUnitIntervalRatio (R._+_ x h)) →
  R._≃_
    (originalNormalizedFiniteExpCross
      stage x (R._+_ x h) xInside yInside)
    (R._*_ h
      (R._+_
        (Cross.sourceODEForcing stage x)
        (R._*_ (Cross.oneMinus x)
          (R._-_
            (Cross.sourceErrorQuotient stage x h)
            (Cross.sourceErrorSlope stage x)))))
originalNormalizedFiniteExpIncrementIsResidualPlusDefect
    stage x h xInside yInside =
  RP.≃-trans
    (originalNormalizedFiniteExpCrossIsSourceCross
      stage x (R._+_ x h) xInside yInside)
    (Cocycle.sourceCrossAtResidualPlusDefect stage x h)
