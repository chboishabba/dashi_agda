module DASHI.Analysis.BishopOriginalNegativeLogFiniteExpCrossWeightTransportExact where

------------------------------------------------------------------------
-- K04d P0: ORIGINAL EXPONENTIAL CROSS-WEIGHT TRANSPORT.
--
-- Source-consuming same-object theorem:
--   (1-x) F_N(x+h) - (1-x-h) F_N(x)
--     ~= (1-x) E_N(x+h) - (1-x-h) E_N(x)
--     ~= h (x^N F_N(x) +
--            (1-x) (q_E(N,x,h) - E_N'(x))).
--
-- The comparison is exact for every stage, point and increment,
-- including h=0. No inverse, interval integration, MVT, FTC,
-- synthetic exponential or derivative-limit interchange occurs.
-- The remaining terminal P0 inequality genuinely needs a
-- UNIFORM source quotient-minus-slope modulus plus finite mesh
-- normalized endpoint transport.
--
-- Original source owners: pinned Bishop/Bridges/Murray/Csimma
-- real and exponential; DASHI finite LOG, factor derivative,
-- finite ODE and cross-weighted derivative authors.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Unnormalised using (1ℚᵘ)
import Real as R
import RealProperties as RP

import DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact as Finite
import DASHI.Analysis.BishopOriginalNegativeLogCrossWeightedIncrementExact as Cross

sourceFiniteExpCrossWeightedIncrement :
  (stage : Nat) (x h : R.ℝ) → R.ℝ
sourceFiniteExpCrossWeightedIncrement stage x h =
  R._-_
    (R._*_ (Cross.oneMinus x)
      (Finite.originalNegativeLogFiniteExponential
        (R._+_ x h) stage))
    (R._*_ (Cross.oneMinus (R._+_ x h))
      (Finite.originalNegativeLogFiniteExponential x stage))

-- Target terms (1-x)(1-x-h) cancel directly and completely.
-- In particular, the residual transport really is for the
-- ORIGINAL exp_B applied to the ORIGINAL finite LOG sum.
originalFiniteExpCrossWeightIsOriginalErrorCrossWeight :
  (stage : Nat) (x h : R.ℝ) →
  R._≃_
    (sourceFiniteExpCrossWeightedIncrement stage x h)
    (Cross.crossWeightedIncrement stage x h)
originalFiniteExpCrossWeightIsOriginalErrorCrossWeight stage x h =
  let
    fNow = Finite.originalNegativeLogFiniteExponential x stage
    fNext =
      Finite.originalNegativeLogFiniteExponential (R._+_ x h) stage
    open RP.ℝ-Solver
  in
  solve 4
    (λ xx hh current next →
      ((Κ 1ℚᵘ ⊖ xx) ⊗ next)
        ⊖ ((Κ 1ℚᵘ ⊖ (xx ⊕ hh)) ⊗ current)
      ⊜
      ((Κ 1ℚᵘ ⊖ xx) ⊗
        (next ⊖ (Κ 1ℚᵘ ⊖ (xx ⊕ hh))))
        ⊖
      ((Κ 1ℚᵘ ⊖ (xx ⊕ hh)) ⊗
        (current ⊖ (Κ 1ℚᵘ ⊖ xx))))
    RP.≃-refl x h fNow fNext

-- This transports the previously proved ORIGINAL finite ODE and
-- quotient defect directly onto the source finite exponential.
-- It is a precise reduction, not a terminal endpoint bound.
originalFiniteExpCrossWeightIsResidualPlusDefect :
  (stage : Nat) (x h : R.ℝ) →
  R._≃_
    (sourceFiniteExpCrossWeightedIncrement stage x h)
    (R._*_ h
      (R._+_
        (Cross.sourceODEForcing stage x)
        (R._*_ (Cross.oneMinus x)
          (R._-_
            (Cross.sourceErrorQuotient stage x h)
            (Cross.sourceErrorSlope stage x)))))
originalFiniteExpCrossWeightIsResidualPlusDefect stage x h =
  RP.≃-trans
    (originalFiniteExpCrossWeightIsOriginalErrorCrossWeight
      stage x h)
    (Cross.originalCrossWeightedIncrementIsResidualPlusDefect
      stage x h)
