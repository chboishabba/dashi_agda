{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopK04dOriginalPolynomialChartTermContinuityExact where

------------------------------------------------------------------------
-- K04d-CONTINUITY: ORIGINAL COMPLEX DIRICHLET TERMS ON THE ACTUAL
-- RE(s)>2 POLYNOMIAL CHART, WITHOUT A SIN/COS CONTINUITY AXIOM.
--
-- The selected chart is s_eta(t)=(3+t*t)+i*eta. For EACH actual
-- original candidate log L_n, -Im(s_eta(t))*L_n=-eta*L_n is a
-- CONSTANT Bishop real as t varies. Thus the literal source
--
--   Re exp_C(-s_eta(t)L_n) = exp_B(-Re(s_eta(t))*L_n)
--                             * cos_B(-eta*L_n)
--   Im exp_C(-s_eta(t)L_n) = exp_B(-Re(s_eta(t))*L_n)
--                             * sin_B(-eta*L_n).
--
-- The two trig factors are constants on this chart. We therefore
-- need ONLY the original exp_B continuity already source-written
-- in BishopOriginalExponentialSequentialContinuityExact, not the
-- missing general imaginary-direction trig continuity.
--
-- This module proves native sequential continuity for:
--   (1) EACH literal selected original Dirichlet term, Re and Im,
--   (2) EVERY finite original source Dirichlet partial, Re and Im,
--   (3) under ONE original exp(-L)=1-x input, the actual Basel
--       uniformly-approximated original Bishop Dirichlet limit
--       along the concrete Re>2 chart, Re and Im.
--
-- THIS IS NOT equality with abstract ZetaHalfPlaneLayer.zetaHalfPlane
-- or CompletedRiemannZeta.xi. That original same-object semantic
-- identification remains an independent terminal gate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)

import Real as R
import Sequence as Seq

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as A
import DASHI.Analysis.BishopSetoidComplexExact as C
import DASHI.Analysis.BishopRiemannDirichletBaselSameObjectExact as Dirichlet
import DASHI.Analysis.BishopRiemannDirichletExponentialTermExact as Terms
import DASHI.Analysis.BishopUniformLimitSequentialContinuityExact as U
import DASHI.Analysis.BishopSequentialContinuityRingCompilerExact as Ring
import DASHI.Analysis.BishopOriginalExponentialSequentialContinuityExact as ExpCont
import DASHI.Analysis.BishopK04dConcreteAboveTwoPolynomialChartExact as Chart
import DASHI.Analysis.BishopK04dNatLogFromOriginalGapExact as NatLog
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as E
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

sourceChartRealExponent :
  (eta : R.ℝ) (logNat : Terms.NatLogCandidate) (index : Nat) →
  R.ℝ → R.ℝ
sourceChartRealExponent eta logNat index t =
  R._*_
    (R.-_ (A.re (Chart.sourcePolynomialChart eta t)))
    (logNat index)

sourceChartImagExponent :
  (eta : R.ℝ) (logNat : Terms.NatLogCandidate) (index : Nat) →
  R.ℝ
sourceChartImagExponent eta logNat index =
  R._*_ (R.-_ eta) (logNat index)

sourceChartRealExponentContinuous :
  (eta : R.ℝ) (logNat : Terms.NatLogCandidate) (index : Nat) →
  U.SequentiallyContinuous (sourceChartRealExponent eta logNat index)
sourceChartRealExponentContinuous eta logNat index =
  Ring.sequentiallyContinuousMultiply
    (λ t → R.-_ (A.re (Chart.sourcePolynomialChart eta t)))
    (λ _ → logNat index)
    (Ring.sequentiallyContinuousNegate
      (λ t → A.re (Chart.sourcePolynomialChart eta t))
      (Chart.sourcePolynomialChartRealContinuous eta))
    (Ring.sequentiallyContinuousConstant (logNat index))

sourceChartExponentialFactorContinuous :
  (eta : R.ℝ) (logNat : Terms.NatLogCandidate) (index : Nat) →
  U.SequentiallyContinuous
    (λ t → Exp.bishopExp (sourceChartRealExponent eta logNat index t))
sourceChartExponentialFactorContinuous eta logNat index input limit converges =
  ExpCont.originalBishopExpSequentiallyContinuous
    (λ n → sourceChartRealExponent eta logNat index (input n))
    (sourceChartRealExponent eta logNat index limit)
    (sourceChartRealExponentContinuous eta logNat index
      input limit converges)

sourceOriginalTerm :
  (inputs : Round11.Round11BishopCutset) →
  (logNat : Terms.NatLogCandidate) (eta : R.ℝ) →
  R.ℝ → Nat → A.BishopComplex
sourceOriginalTerm inputs logNat eta t index =
  Terms.bishopDirichletExponentialTerm
    (Route.round11MachinTranscendentals inputs)
    logNat (Chart.sourcePolynomialChart eta t) index

sourceOriginalTermRealContinuous :
  (inputs : Round11.Round11BishopCutset) →
  (logNat : Terms.NatLogCandidate) (eta : R.ℝ) →
  (index : Nat) →
  U.SequentiallyContinuous
    (λ t → A.re (sourceOriginalTerm inputs logNat eta t index))
sourceOriginalTermRealContinuous inputs logNat eta index =
  let
    T = Route.round11MachinTranscendentals inputs
    c = E.bishopCos (C.dataSet T)
          (sourceChartImagExponent eta logNat index)
  in
  Ring.sequentiallyContinuousMultiply
    (λ t → Exp.bishopExp (sourceChartRealExponent eta logNat index t))
    (λ _ → c)
    (sourceChartExponentialFactorContinuous eta logNat index)
    (Ring.sequentiallyContinuousConstant c)

sourceOriginalTermImagContinuous :
  (inputs : Round11.Round11BishopCutset) →
  (logNat : Terms.NatLogCandidate) (eta : R.ℝ) →
  (index : Nat) →
  U.SequentiallyContinuous
    (λ t → A.im (sourceOriginalTerm inputs logNat eta t index))
sourceOriginalTermImagContinuous inputs logNat eta index =
  let
    T = Route.round11MachinTranscendentals inputs
    c = E.bishopSin (C.dataSet T)
          (sourceChartImagExponent eta logNat index)
  in
  Ring.sequentiallyContinuousMultiply
    (λ t → Exp.bishopExp (sourceChartRealExponent eta logNat index t))
    (λ _ → c)
    (sourceChartExponentialFactorContinuous eta logNat index)
    (Ring.sequentiallyContinuousConstant c)

sourceOriginalFinitePartialRealContinuous :
  (inputs : Round11.Round11BishopCutset) →
  (logNat : Terms.NatLogCandidate) (eta : R.ℝ) →
  (count : Nat) →
  U.SequentiallyContinuous
    (λ t →
      A.re (Dirichlet.dirichletPartial
        (Terms.bishopDirichletExponentialTerm
          (Route.round11MachinTranscendentals inputs)
          logNat)
        (Chart.sourcePolynomialChart eta t)
        count))
sourceOriginalFinitePartialRealContinuous inputs logNat eta zero =
  Ring.sequentiallyContinuousConstant R.0ℝ
sourceOriginalFinitePartialRealContinuous inputs logNat eta (suc count) =
  Ring.sequentiallyContinuousAdd
    (λ t → A.re (Dirichlet.dirichletPartial
      (Terms.bishopDirichletExponentialTerm
        (Route.round11MachinTranscendentals inputs) logNat)
      (Chart.sourcePolynomialChart eta t) count))
    (λ t → A.re (sourceOriginalTerm inputs logNat eta t count))
    (sourceOriginalFinitePartialRealContinuous inputs logNat eta count)
    (sourceOriginalTermRealContinuous inputs logNat eta count)

sourceOriginalFinitePartialImagContinuous :
  (inputs : Round11.Round11BishopCutset) →
  (logNat : Terms.NatLogCandidate) (eta : R.ℝ) →
  (count : Nat) →
  U.SequentiallyContinuous
    (λ t →
      A.im (Dirichlet.dirichletPartial
        (Terms.bishopDirichletExponentialTerm
          (Route.round11MachinTranscendentals inputs)
          logNat)
        (Chart.sourcePolynomialChart eta t)
        count))
sourceOriginalFinitePartialImagContinuous inputs logNat eta zero =
  Ring.sequentiallyContinuousConstant R.0ℝ
sourceOriginalFinitePartialImagContinuous inputs logNat eta (suc count) =
  Ring.sequentiallyContinuousAdd
    (λ t → A.im (Dirichlet.dirichletPartial
      (Terms.bishopDirichletExponentialTerm
        (Route.round11MachinTranscendentals inputs) logNat)
      (Chart.sourcePolynomialChart eta t) count))
    (λ t → A.im (sourceOriginalTerm inputs logNat eta t count))
    (sourceOriginalFinitePartialImagContinuous inputs logNat eta count)
    (sourceOriginalTermImagContinuous inputs logNat eta count)

-- The ONLY still-unproved analytic precondition here is the actual
-- source Bishop negative-log composition; product and exp/trig
-- finite-term continuity are all derived from existing source proofs.
module NativeNatLogOriginalChartContinuous
  (inputs : Round11.Round11BishopCutset)
  (sourceLogIdentity : NatLog.OriginalBishopNegativeLogExponentialGap)
  (eta : R.ℝ)
  where

  module Selected =
    Chart.OriginalNatLogPolynomialChart inputs sourceLogIdentity eta

  originalRealDirichletLimitSequentiallyContinuous :
    U.SequentiallyContinuous Selected.Actual.selectedRealLimit
  originalRealDirichletLimitSequentiallyContinuous =
    Selected.selectedOriginalRealContinuityFromFiniteExp
      (sourceOriginalFinitePartialRealContinuous
        inputs Terms.sourceCanonicalNatLogCandidate eta)

  originalImagDirichletLimitSequentiallyContinuous :
    U.SequentiallyContinuous Selected.Actual.selectedImagLimit
  originalImagDirichletLimitSequentiallyContinuous =
    Selected.selectedOriginalImagContinuityFromFiniteExp
      (sourceOriginalFinitePartialImagContinuous
        inputs Terms.sourceCanonicalNatLogCandidate eta)
