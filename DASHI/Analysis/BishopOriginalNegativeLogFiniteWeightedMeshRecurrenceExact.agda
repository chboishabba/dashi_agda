module DASHI.Analysis.BishopOriginalNegativeLogFiniteWeightedMeshRecurrenceExact where

------------------------------------------------------------------------
-- K04d P0: ALL-FINITE-MESH ORIGINAL SOURCE CROSS-WEIGHT RECURRENCE
--
-- The earlier three-vertex cocycle is extended inductively to
-- arbitrary finite meshes, with no inverse, FTC, MVT, or limit.
--
-- Let v_n be the original Bishop finiteWalk 0 steps n, w(x)=1-x,
-- D_N(a,b)=w(a)F_N(b)-w(b)F_N(a) for original F_N.
-- Define P_0=1, P_(n+1)=P_n*w(v_(n+1)).
-- Define B_0=D_N(v_0,v_1) and
-- B_(n+1)=P_n*w(v_0)*D_N(v_(n+1),v_(n+2))
--           +w(v_(n+2))*B_n.
--
-- Then P_n*D_N(v_0,v_(n+1))=B_n for EVERY n.
-- A second induction replaces every local D_N with the ACTUAL
-- original source h*(residual + w*quotient-defect).
--
-- The result is an exact finite-stage and all-cell transport,
-- not the remaining uniform error inequality / LOG identity.
--
-- Source owners: Bishop/Bridges; pinned Murray/Csimma Real.ℝ;
-- DASHI original finite EXP/LOG, factor derivative, cocycle.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised using (1ℚᵘ)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopOriginalFactorIncrementFiniteTelescopeExact as Walk
import DASHI.Analysis.BishopOriginalNegativeLogCrossWeightedIncrementExact as Cross
import DASHI.Analysis.BishopOriginalNegativeLogCrossWeightCocycleExact as Cocycle

sourceVertex :
  (steps : Nat → R.ℝ) → Nat → R.ℝ
sourceVertex steps = Walk.finiteWalk R.0ℝ steps

sourcePrefixWeight :
  (steps : Nat → R.ℝ) → Nat → R.ℝ
sourcePrefixWeight steps zero = R.1ℝ
sourcePrefixWeight steps (suc n) =
  R._*_
    (sourcePrefixWeight steps n)
    (Cross.oneMinus (sourceVertex steps (suc n)))

sourceScaledEndpoint :
  (stage : Nat) (steps : Nat → R.ℝ) → Nat → R.ℝ
sourceScaledEndpoint stage steps n =
  R._*_
    (sourcePrefixWeight steps n)
    (Cocycle.sourceCrossAt stage
      (sourceVertex steps zero)
      (sourceVertex steps (suc n)))

-- Exact all-cell algebraic budget, retaining the ORIGINAL source
-- exponential at each mesh vertex.
sourceCrossBudget :
  (stage : Nat) (steps : Nat → R.ℝ) → Nat → R.ℝ
sourceCrossBudget stage steps zero =
  Cocycle.sourceCrossAt stage
    (sourceVertex steps zero)
    (sourceVertex steps (suc zero))
sourceCrossBudget stage steps (suc n) =
  R._+_
    (R._*_
      (R._*_
        (sourcePrefixWeight steps n)
        (Cross.oneMinus (sourceVertex steps zero)))
      (Cocycle.sourceCrossAt stage
        (sourceVertex steps (suc n))
        (sourceVertex steps (suc (suc n)))))
    (R._*_
      (Cross.oneMinus (sourceVertex steps (suc (suc n))))
      (sourceCrossBudget stage steps n))

originalFiniteSourceScaledEndpointIsCrossBudget :
  (stage : Nat) (steps : Nat → R.ℝ) (n : Nat) →
  R._≃_
    (sourceScaledEndpoint stage steps n)
    (sourceCrossBudget stage steps n)
originalFiniteSourceScaledEndpointIsCrossBudget stage steps zero =
  RP.*-identityˡ
    (Cocycle.sourceCrossAt stage
      (sourceVertex steps zero)
      (sourceVertex steps (suc zero)))
originalFiniteSourceScaledEndpointIsCrossBudget stage steps (suc n) =
  let
    p = sourcePrefixWeight steps n
    a = sourceVertex steps zero
    b = sourceVertex steps (suc n)
    c = sourceVertex steps (suc (suc n))
    anchor = Cocycle.sourceCrossAt stage a b
    local = Cocycle.sourceCrossAt stage b c
    endpoint = Cocycle.sourceCrossAt stage a c
    wa = Cross.oneMinus a
    wb = Cross.oneMinus b
    wc = Cross.oneMinus c
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (solve 3
      (λ pp ww dd → (pp ⊗ ww) ⊗ dd ⊜ pp ⊗ (ww ⊗ dd))
      RP.≃-refl p wb endpoint)
    (RP.≃-trans
      (RP.*-cong
        RP.≃-refl
        (Cocycle.originalSourceCrossThreeVertexCocycle
          stage a b c))
      (RP.≃-trans
        (solve 5
          (λ pp aa ll cc rr →
            pp ⊗ ((aa ⊗ ll) ⊕ (cc ⊗ rr))
            ⊜ ((pp ⊗ aa) ⊗ ll) ⊕
              (cc ⊗ (pp ⊗ rr)))
          RP.≃-refl p wa local wc anchor)
        (RP.+-cong RP.≃-refl
          (RP.*-cong RP.≃-refl
            (originalFiniteSourceScaledEndpointIsCrossBudget
              stage steps n)))))

-- Each local term is precisely the original finite EXP residual
-- plus its actual error-factor quotient defect.
sourceResidualCell :
  (stage : Nat) (x h : R.ℝ) → R.ℝ
sourceResidualCell stage x h =
  R._*_ h
    (R._+_
      (Cross.sourceODEForcing stage x)
      (R._*_ (Cross.oneMinus x)
        (R._-_
          (Cross.sourceErrorQuotient stage x h)
          (Cross.sourceErrorSlope stage x))))

sourceResidualBudget :
  (stage : Nat) (steps : Nat → R.ℝ) → Nat → R.ℝ
sourceResidualBudget stage steps zero =
  sourceResidualCell stage
    (sourceVertex steps zero) (steps zero)
sourceResidualBudget stage steps (suc n) =
  R._+_
    (R._*_
      (R._*_
        (sourcePrefixWeight steps n)
        (Cross.oneMinus (sourceVertex steps zero)))
      (sourceResidualCell stage
        (sourceVertex steps (suc n))
        (steps (suc n))))
    (R._*_
      (Cross.oneMinus (sourceVertex steps (suc (suc n))))
      (sourceResidualBudget stage steps n))

originalFiniteSourceCrossBudgetIsResidualBudget :
  (stage : Nat) (steps : Nat → R.ℝ) (n : Nat) →
  R._≃_
    (sourceCrossBudget stage steps n)
    (sourceResidualBudget stage steps n)
originalFiniteSourceCrossBudgetIsResidualBudget stage steps zero =
  Cocycle.sourceCrossAtResidualPlusDefect
    stage (sourceVertex steps zero) (steps zero)
originalFiniteSourceCrossBudgetIsResidualBudget stage steps (suc n) =
  RP.+-cong
    (RP.*-cong RP.≃-refl
      (Cocycle.sourceCrossAtResidualPlusDefect
        stage (sourceVertex steps (suc n)) (steps (suc n))))
    (RP.*-cong RP.≃-refl
      (originalFiniteSourceCrossBudgetIsResidualBudget
        stage steps n))

-- Terminal all-finite-mesh cross-weight equality. It is not a
-- numerical upper bound: the quotient defects remain explicit.
originalFiniteSourceScaledEndpointIsResidualBudget :
  (stage : Nat) (steps : Nat → R.ℝ) (n : Nat) →
  R._≃_
    (sourceScaledEndpoint stage steps n)
    (sourceResidualBudget stage steps n)
originalFiniteSourceScaledEndpointIsResidualBudget stage steps n =
  RP.≃-trans
    (originalFiniteSourceScaledEndpointIsCrossBudget
      stage steps n)
    (originalFiniteSourceCrossBudgetIsResidualBudget
      stage steps n)
