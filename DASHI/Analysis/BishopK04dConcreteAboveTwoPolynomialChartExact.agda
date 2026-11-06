{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopK04dConcreteAboveTwoPolynomialChartExact where

------------------------------------------------------------------------
-- K04d-CONTINUITY: A CONCRETE TOTAL CHART IN THE ORIGINAL Re(s)>2
-- SOURCE REGION (NO ARBITRARY "inside" CHART MEMBERSHIP ASSUMPTION).
--
-- Construct, for each fixed selected Bishop imaginary parameter eta:
--    s_eta(t) = (3 + t²) + i eta.
--
-- This maps EVERY Bishop real t into the original Re(s)>2 region
-- because 2<3 and t²>=0 constructively in the original pinned
-- Bishop real order. Both coordinates are sequentially continuous
-- using the already-written ORIGINAL native Sequence ring proof.
--
-- The original canonical complex Dirichlet term family is
--   exp_C(-s*L_n), not an integer-only artificial series.
-- Its actual region-wide Basel domination follows from precisely:
--    1. ONE original exp_B(-L(x))~1-x analytic identity;
--    2. the SOURCE-WRITTEN K05 signed-factorial Cauchy product theorem.
-- This supplies the concrete uniform approximation proof.
--
-- The remaining finite-exp-term continuity and SAME original zeta/xi
-- function identification are explicitly not inferred by this module.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (_/_)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (toWitness)

import Real as R
import RealProperties as RP

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as A
import DASHI.Analysis.BishopRiemannComplexAboveTwoBaselExact as Region
import DASHI.Analysis.BishopRiemannDirichletExponentialTermExact as Terms
import DASHI.Analysis.BishopDirichletUniformBaselTailsExact as UniformTails
import DASHI.Analysis.BishopDirichletUniformLimitContinuityCompilerExact as Compiler
import DASHI.Analysis.BishopUniformLimitSequentialContinuityExact as Uniform
import DASHI.Analysis.BishopSequentialContinuityRingCompilerExact as Ring
import DASHI.Analysis.BishopMachinCayleyNativeProductFirstZeroExact as Native
import DASHI.Analysis.BishopK04dNatLogFromOriginalGapExact as NatLog
import DASHI.Foundations.BishopSquareNonnegativeExact as Square
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

bishopThree : R.ℝ
bishopThree = R._⋆ (+ 3 / 1)

twoBelowThree : R._<_ Terms.sourceTwoReal bishopThree
twoBelowThree =
  RP.p<q⇒p⋆<q⋆
    (+ 2 / 1) (+ 3 / 1)
    (toWitness {a? = QP._<?_ (+ 2 / 1) (+ 3 / 1)} _)

threeBelowThreePlusSquare :
  (t : R.ℝ) →
  R._≤_
    bishopThree
    (R._+_ bishopThree (R._*_ t t))
threeBelowThreePlusSquare t =
  RP.≤-respˡ-≃
    (RP.+-identityʳ bishopThree)
    (RP.+-monoʳ-≤
      bishopThree
      (RP.nonNegx⇒0≤x
        (Square.bishopSquareNonnegative t)))

-- The chart is in the SAME Bishop Cartesian complex as the original
-- Dirichlet and completed-zeta analytic carrier.
sourcePolynomialChart : R.ℝ → R.ℝ → A.BishopComplex
sourcePolynomialChart eta t =
  A.bishop-complex
    (R._+_ bishopThree (R._*_ t t))
    eta

sourcePolynomialChartInsideAboveTwo :
  (eta t : R.ℝ) →
  Region.sourceAboveTwoRegion (sourcePolynomialChart eta t)
sourcePolynomialChartInsideAboveTwo eta t =
  RP.<-≤-trans
    twoBelowThree
    (threeBelowThreePlusSquare t)

sourcePolynomialChartRealContinuous :
  (eta : R.ℝ) →
  Uniform.SequentiallyContinuous
    (λ t → A.re (sourcePolynomialChart eta t))
sourcePolynomialChartRealContinuous eta =
  Ring.sequentiallyContinuousAdd
    (λ _ → bishopThree)
    (λ t → R._*_ t t)
    (Ring.sequentiallyContinuousConstant bishopThree)
    (Ring.sequentiallyContinuousMultiply
      (λ t → t) (λ t → t)
      Ring.sequentiallyContinuousIdentity
      Ring.sequentiallyContinuousIdentity)

sourcePolynomialChartImagContinuous :
  (eta : R.ℝ) →
  Uniform.SequentiallyContinuous
    (λ t → A.im (sourcePolynomialChart eta t))
sourcePolynomialChartImagContinuous eta =
  Ring.sequentiallyContinuousConstant eta

------------------------------------------------------------------------
-- Concrete domain-valid selected original Bishop Dirichlet chart.
-- The original K05 product is consumed *as a theorem*, not as a
-- user-supplied parameter. Only K04d-LOG's one analytic identity
-- remains to establish the source Basel majorant.
------------------------------------------------------------------------

module OriginalNatLogPolynomialChart
  (inputs : Round11.Round11BishopCutset)
  (sourceLogIdentity : NatLog.OriginalBishopNegativeLogExponentialGap)
  (eta : R.ℝ)
  where

  sourceTerms = Terms.bishopDirichletExponentialTerm
    (Route.round11MachinTranscendentals inputs)
    Terms.sourceCanonicalNatLogCandidate

  sourceBasel =
    Native.sourceRegionBaselFromOneNativeLogIdentity
      inputs sourceLogIdentity

  module Actual =
    Compiler.OnSelectedChart
      sourceTerms
      Region.sourceAboveTwoRegion
      sourceBasel
      (sourcePolynomialChart eta)
      (sourcePolynomialChartInsideAboveTwo eta)

  selectedOriginalRealUniformApproximation :
    Uniform.UniformApproximation
      Actual.partialReal Actual.selectedRealLimit
  selectedOriginalRealUniformApproximation =
    Actual.originalUniformRealApproximation

  selectedOriginalImagUniformApproximation :
    Uniform.UniformApproximation
      Actual.partialImag Actual.selectedImagLimit
  selectedOriginalImagUniformApproximation =
    Actual.originalUniformImagApproximation

  selectedOriginalRealContinuityFromFiniteExp :
    (∀ count →
      Uniform.SequentiallyContinuous (Actual.partialReal count)) →
    Uniform.SequentiallyContinuous Actual.selectedRealLimit
  selectedOriginalRealContinuityFromFiniteExp =
    Actual.selectedDirichletRealSequentiallyContinuous

  selectedOriginalImagContinuityFromFiniteExp :
    (∀ count →
      Uniform.SequentiallyContinuous (Actual.partialImag count)) →
    Uniform.SequentiallyContinuous Actual.selectedImagLimit
  selectedOriginalImagContinuityFromFiniteExp =
    Actual.selectedDirichletImagSequentiallyContinuous
