{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalNegativeLogExpFiniteStageLimitExact where

------------------------------------------------------------------------
-- K04d-P0: LITERAL FINITE COMPOSITION CONVERGES TO THE ORIGINAL EXP
-- EVALUATION, NOT A SECOND LOG/EXP CARRIER.
--
-- SourceNegativeLogValue x is the actual Bishop SeriesOf limit of
-- (x^(n+1)/(n+1)) at 0<x<1. The original Bishop exponential is
-- source-proved sequentially continuous.
--
-- It follows WITHOUT ANY FURTHER ANALYTIC HYPOTHESIS that the
-- original exp of each literal NEGATIVE finite partial sum converges
-- to exp of the original infinite negative-log source series:
--
--     exp_B(-L_N(x)) -> exp_B(-L_B(x)).
--
-- This pays the actual nested-source "continuity of composition"
-- subgate. Hence the terminal LOG value equality is precisely reduced
-- to showing these SAME finite compositions converge to 1-x.
--
-- The result is NOT a proof that their limit is 1-x. That last
-- evaluation must come from a genuine finite-stage estimate or
-- source-native convergent formal-series identity; it cannot be
-- supplied by an arbitrary Set-valued identification.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Foundations.BishopNegativeLogGeometricSourceConvergenceExact as Log
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Analysis.BishopOriginalExponentialSequentialContinuityExact as ExpContinuity

-- This is the actual source partial-sum function, not a generic
-- logarithm or newly selected arbitrary approximation history.
originalLogFinitePartial : R.ℝ → Nat → R.ℝ
originalLogFinitePartial x n =
  Seq.SeriesOf (Log.sourceNegativeLogTerm x) n

originalNegativeLogFiniteExponential : R.ℝ → Nat → R.ℝ
originalNegativeLogFiniteExponential x n =
  Exp.bishopExp (R.-_ (originalLogFinitePartial x n))

-- The source finite log partial sums tend to their actual limit,
-- so the actual negatives tend to the negative of that same limit.
originalNegativeLogFiniteInputsConverge :
  (x : R.ℝ) →
  (positive : R._<_ R.0ℝ x) →
  (belowOne : R._<_ x R.1ℝ) →
  Seq._ConvergesTo_
    (λ n → R.-_ (originalLogFinitePartial x n))
    (R.-_ (Log.sourceNegativeLogValue x positive belowOne))
originalNegativeLogFiniteInputsConverge x positive belowOne =
  Seq.-xₙ→-x₀
    (Log.sourceNegativeLogValue x positive belowOne ,
      Log.sourceNegativeLogValueConverges x positive belowOne)

-- Unconditional source-native original composition convergence.
originalNegativeLogFiniteExponentialConverges :
  (x : R.ℝ) →
  (positive : R._<_ R.0ℝ x) →
  (belowOne : R._<_ x R.1ℝ) →
  Seq._ConvergesTo_
    (originalNegativeLogFiniteExponential x)
    (Exp.bishopExp
      (R.-_ (Log.sourceNegativeLogValue x positive belowOne)))
originalNegativeLogFiniteExponentialConverges x positive belowOne =
  ExpContinuity.originalBishopExpSequentiallyContinuous
    (λ n → R.-_ (originalLogFinitePartial x n))
    (R.-_ (Log.sourceNegativeLogValue x positive belowOne))
    (originalNegativeLogFiniteInputsConverge x positive belowOne)

-- FINITE-EVALUATION -> ORIGINAL LOG, using unique Bishop limits.
-- The only premise is the precise convergence of the ORIGINAL
-- finite-stage compositions to 1-x, not a free logarithm definition.
originalNegativeLogTerminalFromFiniteEvaluation :
  (x : R.ℝ) →
  (positive : R._<_ R.0ℝ x) →
  (belowOne : R._<_ x R.1ℝ) →
  Seq._ConvergesTo_
    (originalNegativeLogFiniteExponential x)
    (R._-_ R.1ℝ x) →
  R._≃_
    (Exp.bishopExp
      (R.-_ (Log.sourceNegativeLogValue x positive belowOne)))
    (R._-_ R.1ℝ x)
originalNegativeLogTerminalFromFiniteEvaluation
    x positive belowOne finiteEvaluation =
  Seq.uniqueness-of-limits
    (originalNegativeLogFiniteExponentialConverges
      x positive belowOne)
    finiteEvaluation

-- ORIGINAL LOG -> FINITE-EVALUATION, so this reduction is an
-- equivalence of *genuine source convergence goals*, not a mere
-- one-way conditional compiler.
originalNegativeLogFiniteEvaluationFromTerminal :
  (x : R.ℝ) →
  (positive : R._<_ R.0ℝ x) →
  (belowOne : R._<_ x R.1ℝ) →
  R._≃_
    (Exp.bishopExp
      (R.-_ (Log.sourceNegativeLogValue x positive belowOne)))
    (R._-_ R.1ℝ x) →
  Seq._ConvergesTo_
    (originalNegativeLogFiniteExponential x)
    (R._-_ R.1ℝ x)
originalNegativeLogFiniteEvaluationFromTerminal
    x positive belowOne terminal =
  Seq.xₙ→x∧x≃y⇒xₙ→y
    (originalNegativeLogFiniteExponentialConverges
      x positive belowOne)
    terminal
