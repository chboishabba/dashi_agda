{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalCompletedZetaUniformChartContinuityExact where

------------------------------------------------------------------------
-- K04d: ORIGINAL COMPLETED RIEMANN ZETA, NOT A SYNTHETIC REPLACEMENT.
--
-- Once the ORIGINAL ZetaHalfPlaneLayer is identified pointwise with
-- the genuine Basel-dominated Bishop Dirichlet series, its original
-- CompletedRiemannZeta agreesWithHalfPlane proof gives the same object
-- in both Bishop coordinates.
--
-- The selected Dirichlet chart already owns a single uniform Basel
-- cutoff via BishopDirichletUniformBaselTailsExact, and the newly
-- native Bishop uniform-limit theorem transports continuity from
-- the finite partial sums. This module stitches them together;
-- it does NOT declare opaque Meromorphic implies continuous.
--
-- The original half-plane agreement and actual finite term
-- continuity remain explicit SOURCE-SIDE analytic proof targets,
-- rather than secretly constructed data or propositions filled by
-- a generic record constructor.
--
-- Riemann 1859; Bishop and Bridges; Cauchy; Murray 2022 and pinned
-- Csimma Bishop carrier; original DASHI K04d analytic function layer.
-- Source-written, Agda-2.9 kernel acceptance pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)

import Real as R
import RealProperties as RP
import Sequence as Seq

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.BishopRiemannDirichletBaselSameObjectExact as Dirichlet
import DASHI.Analysis.BishopDirichletUniformBaselTailsExact as Tails
import DASHI.Analysis.BishopDirichletUniformLimitContinuityCompilerExact as Compiler
import DASHI.Analysis.BishopUniformLimitSequentialContinuityExact as Uniform

pointwiseEquivalentPreservesSequentialContinuity :
  (original selected : R.ℝ → R.ℝ) →
  (∀ x → R._≃_ (original x) (selected x)) →
  Uniform.SequentiallyContinuous selected →
  Uniform.SequentiallyContinuous original
pointwiseEquivalentPreservesSequentialContinuity
    original selected originalIsSelected selectedContinuous
    input limit inputConverges =
  Seq.xₙ→x∧x≃y⇒xₙ→y
    (Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ {(suc n) →
        RP.≃-symm (originalIsSelected (input (suc n)))})
      (selected limit ,
        selectedContinuous input limit inputConverges))
    (RP.≃-symm (originalIsSelected limit))

module OriginalCompletedChart
  (functions : BC.BishopComplexAnalyticFunctionLayer)
  (gamma : Analytic.GammaMellinLayer
    (BC.bishopComplexAnalyticCarrier functions))
  (halfPlane : Analytic.ZetaHalfPlaneLayer
    (BC.bishopComplexAnalyticCarrier functions))
  (completed : Analytic.CompletedRiemannZeta
    (BC.bishopComplexAnalyticCarrier functions) gamma halfPlane)
  (terms : Dirichlet.BishopDirichletTermFamily)
  (Region : BC.BishopComplex → Set)
  (bound : Tails.RegionBaselDomination terms Region)
  (chart : R.ℝ → BC.BishopComplex)
  (inside : (x : R.ℝ) → Region (chart x))
  (domain : (x : R.ℝ) →
    Analytic.ZetaHalfPlaneLayer.realPartGreaterThanOne halfPlane (chart x))
  (agreement : (x : R.ℝ) →
    Dirichlet.OriginalHalfPlaneDirichletAgreement
      functions halfPlane terms (chart x))
  where

  module Selected =
    Compiler.OnSelectedChart terms Region bound chart inside

  module Original =
    Dirichlet.AtOriginalCompletedZeta
      functions gamma halfPlane completed terms

  originalCompletedReal : R.ℝ → R.ℝ
  originalCompletedReal x =
    BC.re (Original.originalZetaValue (chart x))

  originalCompletedImag : R.ℝ → R.ℝ
  originalCompletedImag x =
    BC.im (Original.originalZetaValue (chart x))

  originalRealIsSelectedDirichlet :
    (x : R.ℝ) →
    R._≃_
      (originalCompletedReal x)
      (Selected.selectedRealLimit x)
  originalRealIsSelectedDirichlet x =
    RP.≃-trans
      (Original.originalCompletedZetaRealAgreesWithDirichlet
        (chart x) (domain x) (agreement x))
      (Dirichlet.dirichletRealValueIndependentOfMajorant
        terms (chart x)
        (Dirichlet.seriesBound (agreement x))
        (Tails.regionPointwiseMajorant
          terms Region bound (chart x) (inside x)))

  originalImagIsSelectedDirichlet :
    (x : R.ℝ) →
    R._≃_
      (originalCompletedImag x)
      (Selected.selectedImagLimit x)
  originalImagIsSelectedDirichlet x =
    RP.≃-trans
      (Original.originalCompletedZetaImagAgreesWithDirichlet
        (chart x) (domain x) (agreement x))
      (Dirichlet.dirichletImagValueIndependentOfMajorant
        terms (chart x)
        (Dirichlet.seriesBound (agreement x))
        (Tails.regionPointwiseMajorant
          terms Region bound (chart x) (inside x)))

  originalCompletedRealSequentiallyContinuous :
    (∀ count →
      Uniform.SequentiallyContinuous (Selected.partialReal count)) →
    Uniform.SequentiallyContinuous originalCompletedReal
  originalCompletedRealSequentiallyContinuous finiteContinuous =
    pointwiseEquivalentPreservesSequentialContinuity
      originalCompletedReal Selected.selectedRealLimit
      originalRealIsSelectedDirichlet
      (Selected.selectedDirichletRealSequentiallyContinuous
        finiteContinuous)

  originalCompletedImagSequentiallyContinuous :
    (∀ count →
      Uniform.SequentiallyContinuous (Selected.partialImag count)) →
    Uniform.SequentiallyContinuous originalCompletedImag
  originalCompletedImagSequentiallyContinuous finiteContinuous =
    pointwiseEquivalentPreservesSequentialContinuity
      originalCompletedImag Selected.selectedImagLimit
      originalImagIsSelectedDirichlet
      (Selected.selectedDirichletImagSequentiallyContinuous
        finiteContinuous)
