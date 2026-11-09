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
