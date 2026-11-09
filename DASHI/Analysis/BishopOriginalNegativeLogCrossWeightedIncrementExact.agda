module DASHI.Analysis.BishopOriginalNegativeLogCrossWeightedIncrementExact where

------------------------------------------------------------------------
-- P0: EXACT CROSS-WEIGHTED INTEGRATING-FACTOR IDENTITY
--
-- For E_N(x)=exp_B(-L_N(x))-(1-x), derivative slope d_N(x),
-- source division-free factor quotient q_N(x,h), and actual
-- forcing R_N(x)=x^N exp_B(-L_N(x)), the pinned Bishop identities
-- imply, with y=x+h:
--
-- (1-x) E_N(y) - (1-y) E_N(x)
--  ~= h * [ R_N(x) + (1-x)*(q_N(x,h)-d_N(x)) ].
--
-- This is a constructive "integrating factor" CROSS-PRODUCT
-- identity requiring NO inverse of 1-x or h. The error's own
-- contribution cancels exactly. Hence the only mesh-analysis
-- debts are:
--  (a) uniform control of original source quotient-minus-slope;
--  (b) finite cross-weight telescoping / endpoint positivity.
--
-- These debts cannot be replaced by uniform pointwise forcing alone.
-- The identity directly reuses the original P0 error derivative
-- and original finite ODE, not any generic field-valued calculus.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Unnormalised using (1ℚᵘ)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopFactorDerivativeExact as Factor
import DASHI.Analysis.BishopOriginalNegativeLogFiniteErrorDerivativeExact as Error
import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite

oneMinus : R.ℝ → R.ℝ
oneMinus x = R._-_ R.1ℝ x

crossWeightedIncrement :
  (stage : Nat) (x h : R.ℝ) → R.ℝ
crossWeightedIncrement stage x h =
  R._-_
    (R._*_ (oneMinus x)
      (Error.originalFiniteLogExpError stage (R._+_ x h)))
    (R._*_ (oneMinus (R._+_ x h))
      (Error.originalFiniteLogExpError stage x))

sourceErrorQuotient :
  (stage : Nat) (x h : R.ℝ) → R.ℝ
sourceErrorQuotient stage x h =
  Factor.quotient
    (Error.originalFiniteLogExpErrorDerivative stage x)
    h

sourceErrorSlope :
  (stage : Nat) (x : R.ℝ) → R.ℝ
sourceErrorSlope = Error.originalFiniteLogExpErrorSlope

sourceODEForcing :
  (stage : Nat) (x : R.ℝ) → R.ℝ
sourceODEForcing stage x =
  R._*_
    (Finite.originalNegativeLogFiniteExponential x stage)
    (R.pow x stage)

-- The cancellation is exact even at h=0; there is no division.
originalCrossWeightedIncrementIsQuotient :
  (stage : Nat) (x h : R.ℝ) →
  R._≃_
    (crossWeightedIncrement stage x h)
    (R._*_ h
      (R._+_
        (R._*_ (oneMinus x)
          (sourceErrorQuotient stage x h))
        (Error.originalFiniteLogExpError stage x)))
originalCrossWeightedIncrementIsQuotient stage x h =
  let
    old = Error.originalFiniteLogExpError stage x
    new = Error.originalFiniteLogExpError stage (R._+_ x h)
    q = sourceErrorQuotient stage x h
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (solve 4
      (λ xx hh oldE newE →
        ((Κ 1ℚᵘ ⊖ xx) ⊗ newE)
          ⊖ ((Κ 1ℚᵘ ⊖ (xx ⊕ hh)) ⊗ oldE)
        ⊜ ((Κ 1ℚᵘ ⊖ xx) ⊗ (newE ⊖ oldE))
          ⊕ (hh ⊗ oldE))
      RP.≃-refl x h old new)
    (RP.≃-trans
      (RP.+-cong
        (RP.*-cong
          RP.≃-refl
          (Factor.incrementFactorisation
            (Error.originalFiniteLogExpErrorDerivative stage x) h))
        RP.≃-refl)
      (solve 4
        (λ xx hh qq oldE →
          ((Κ 1ℚᵘ ⊖ xx) ⊗ (hh ⊗ qq))
            ⊕ (hh ⊗ oldE)
          ⊜ hh ⊗
            (((Κ 1ℚᵘ ⊖ xx) ⊗ qq) ⊕ oldE))
        RP.≃-refl x h q old))

-- EXACT source finite-stage integrating-factor law, no selected
-- ODE interface. The whole error value disappears from the source
-- forcing, leaving only the quotient-vs-derivative defect.
originalCrossWeightedIncrementIsResidualPlusDefect :
  (stage : Nat) (x h : R.ℝ) →
  R._≃_
    (crossWeightedIncrement stage x h)
    (R._*_ h
      (R._+_
        (sourceODEForcing stage x)
        (R._*_ (oneMinus x)
          (R._-_
            (sourceErrorQuotient stage x h)
            (sourceErrorSlope stage x)))))
originalCrossWeightedIncrementIsResidualPlusDefect stage x h =
  let
    e = Error.originalFiniteLogExpError stage x
    d = sourceErrorSlope stage x
    q = sourceErrorQuotient stage x h
    c = oneMinus x
    forcing = sourceODEForcing stage x
    open RP.ℝ-Solver
  in
  RP.≃-trans
    (originalCrossWeightedIncrementIsQuotient stage x h)
    (RP.*-cong
      RP.≃-refl
      (RP.≃-trans
        (solve 4
          (λ cc qq dd ee →
            (cc ⊗ qq) ⊕ ee
            ⊜ ((cc ⊗ dd) ⊕ ee)
              ⊕ (cc ⊗ (qq ⊖ dd)))
          RP.≃-refl c q d e)
        (RP.+-cong
          (Error.originalFiniteLogExpErrorODE stage x)
          RP.≃-refl)))
