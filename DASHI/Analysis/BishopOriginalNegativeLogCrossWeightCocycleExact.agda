module DASHI.Analysis.BishopOriginalNegativeLogCrossWeightCocycleExact where

------------------------------------------------------------------------
-- K04d P0: THREE-VERTEX CROSS-WEIGHT COCYCLE ON ORIGINAL BISHOP REAL.
--
-- For the ORIGINAL F_N(x)=exp_B(-L_N(x)), and w(x)=1-x, define
--   D_N(a,b)=w(a) F_N(b)-w(b) F_N(a).
--
-- Then, for EVERY a,b,c and every finite N:
--   w(b) D_N(a,c) =
--       w(a) D_N(b,c) + w(c) D_N(a,b).
--
-- This is the EXACT two-cell composition law needed to aggregate
-- the prior source-weighted local residual across a mesh. No
-- positive reciprocal, positivity premise, FTC, MVT, or limit is
-- used or assumed. It also holds for the source target error,
-- because the target w terms cancel in the determinant.
--
-- Source ownership: Bishop/Bridges; Murray/Csimma pinned Real.ℝ;
-- DASHI original finite LOG/exp and weighted transport authors.
-- Source-written; Agda 2.9 kernel acceptance still outstanding.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Unnormalised using (1ℚᵘ)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite
import DASHI.Analysis.BishopOriginalNegativeLogFiniteErrorDerivativeExact as Error
import DASHI.Analysis.BishopOriginalNegativeLogCrossWeightedIncrementExact as Cross
import DASHI.Analysis.BishopOriginalNegativeLogFiniteExpCrossWeightTransportExact as Transport

sourceCrossAt :
  (stage : Nat) (a b : R.ℝ) → R.ℝ
sourceCrossAt stage a b =
  R._-_
    (R._*_ (Cross.oneMinus a)
      (Finite.originalNegativeLogFiniteExponential b stage))
    (R._*_ (Cross.oneMinus b)
      (Finite.originalNegativeLogFiniteExponential a stage))

errorCrossAt :
  (stage : Nat) (a b : R.ℝ) → R.ℝ
errorCrossAt stage a b =
  R._-_
    (R._*_ (Cross.oneMinus a)
      (Error.originalFiniteLogExpError stage b))
    (R._*_ (Cross.oneMinus b)
      (Error.originalFiniteLogExpError stage a))

-- The same original target cancellation works at independent
-- vertices, not only at endpoints related by b = a+h.
originalSourceCrossIsErrorCross :
  (stage : Nat) (a b : R.ℝ) →
  R._≃_ (sourceCrossAt stage a b) (errorCrossAt stage a b)
originalSourceCrossIsErrorCross stage a b =
  let
    fa = Finite.originalNegativeLogFiniteExponential a stage
    fb = Finite.originalNegativeLogFiniteExponential b stage
    open RP.ℝ-Solver
  in
  solve 4
    (λ aa bb ffa ffb →
      ((Κ 1ℚᵘ ⊖ aa) ⊗ ffb)
        ⊖ ((Κ 1ℚᵘ ⊖ bb) ⊗ ffa)
      ⊜
      ((Κ 1ℚᵘ ⊖ aa) ⊗
        (ffb ⊖ (Κ 1ℚᵘ ⊖ bb)))
        ⊖
      ((Κ 1ℚᵘ ⊖ bb) ⊗
        (ffa ⊖ (Κ 1ℚᵘ ⊖ aa))))
    RP.≃-refl a b fa fb

-- Three-vertex transport is an exact Pluecker-type determinant
-- identity. No quotient defect can be silently removed here.
originalSourceCrossThreeVertexCocycle :
  (stage : Nat) (a b c : R.ℝ) →
  R._≃_
    (R._*_ (Cross.oneMinus b) (sourceCrossAt stage a c))
    (R._+_
      (R._*_ (Cross.oneMinus a) (sourceCrossAt stage b c))
      (R._*_ (Cross.oneMinus c) (sourceCrossAt stage a b)))
originalSourceCrossThreeVertexCocycle stage a b c =
  let
    fa = Finite.originalNegativeLogFiniteExponential a stage
    fb = Finite.originalNegativeLogFiniteExponential b stage
    fc = Finite.originalNegativeLogFiniteExponential c stage
    open RP.ℝ-Solver
  in
  solve 6
    (λ aa bb cc ffa ffb ffc →
      ((Κ 1ℚᵘ ⊖ bb) ⊗
        (((Κ 1ℚᵘ ⊖ aa) ⊗ ffc)
          ⊖ ((Κ 1ℚᵘ ⊖ cc) ⊗ ffa)))
      ⊜
        ((Κ 1ℚᵘ ⊖ aa) ⊗
          (((Κ 1ℚᵘ ⊖ bb) ⊗ ffc)
            ⊖ ((Κ 1ℚᵘ ⊖ cc) ⊗ ffb)))
        ⊕
        ((Κ 1ℚᵘ ⊖ cc) ⊗
          (((Κ 1ℚᵘ ⊖ aa) ⊗ ffb)
            ⊖ ((Κ 1ℚᵘ ⊖ bb) ⊗ ffa))))
    RP.≃-refl a b c fa fb fc

------------------------------------------------------------------------
-- Source residual on two consecutive cells x -> x+h -> x+h+k.
-- This preserves every quotient defect, in contrast to replacing
-- a positive-step quotient by its derivative at finite mesh size.
------------------------------------------------------------------------

sourceCrossAtIncrement :
  (stage : Nat) (x h : R.ℝ) →
  R._≃_
    (sourceCrossAt stage x (R._+_ x h))
    (Transport.sourceFiniteExpCrossWeightedIncrement stage x h)
sourceCrossAtIncrement stage x h = RP.≃-refl

sourceCrossAtResidualPlusDefect :
  (stage : Nat) (x h : R.ℝ) →
  R._≃_
    (sourceCrossAt stage x (R._+_ x h))
    (R._*_ h
      (R._+_
        (Cross.sourceODEForcing stage x)
        (R._*_ (Cross.oneMinus x)
          (R._-_
            (Cross.sourceErrorQuotient stage x h)
            (Cross.sourceErrorSlope stage x)))))
sourceCrossAtResidualPlusDefect stage x h =
  RP.≃-trans
    (sourceCrossAtIncrement stage x h)
    (Transport.originalFiniteExpCrossWeightIsResidualPlusDefect
      stage x h)

-- The exact two-cell endpoint transport, in terms of original
-- F_N local residual and original quotient defect at each cell.
originalSourceCrossTwoStepResidual :
  (stage : Nat) (x h k : R.ℝ) →
  let
    y = R._+_ x h
    z = R._+_ y k
    local = λ point step →
      R._*_ step
        (R._+_
          (Cross.sourceODEForcing stage point)
          (R._*_ (Cross.oneMinus point)
            (R._-_
              (Cross.sourceErrorQuotient stage point step)
              (Cross.sourceErrorSlope stage point))))
  in
  R._≃_
    (R._*_ (Cross.oneMinus y)
      (sourceCrossAt stage x z))
    (R._+_
      (R._*_ (Cross.oneMinus x) (local y k))
      (R._*_ (Cross.oneMinus z) (local x h)))
originalSourceCrossTwoStepResidual stage x h k =
  let
    y = R._+_ x h
    z = R._+_ y k
  in
  RP.≃-trans
    (originalSourceCrossThreeVertexCocycle stage x y z)
    (RP.+-cong
      (RP.*-cong RP.≃-refl
        (sourceCrossAtResidualPlusDefect stage y k))
      (RP.*-cong RP.≃-refl
        (sourceCrossAtResidualPlusDefect stage x h)))
