{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopDirichletUniformLimitContinuityCompilerExact where

------------------------------------------------------------------------
-- K04d-CONTINUITY: THE ACTUAL DIRICHLET BASEL TAIL OWNER WELDED
-- TO THE PINNED BISHOP UNIFORM-LIMIT CONTINUITY THEOREM.
--
-- This transports the EXISTING Basel-supplied single cutoff N(k)
-- into the actual complex Dirichlet sum on a selected real chart.
-- There is no new uniform convergence authority; the entire modulus
-- is built by BishopDirichletUniformBaselTailsExact.
--
-- One precise input remains: each ORIGINAL finite Dirichlet partial
-- must be sequentially continuous as a function of the argument,
-- and the chart must carry the proved region-membership witness.
-- For exp(-s logNat n) this demands original Bishop exponential
-- continuity and the source logarithm identification. No opaque
-- zeta/meromorphic assumption is used.
--
-- Sources: Dirichlet, Riemann (1859); Basel; Bishop/Bridges;
-- Murray (2022)/pinned Csimma Sequence; DASHI prior K04d owners.
-- Kernel typecheck pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Properties as NatP

import Real as R
import RealProperties as RP

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.BishopRiemannDirichletBaselSameObjectExact as Dirichlet
import DASHI.Analysis.BishopDirichletUniformBaselTailsExact as Tails
import DASHI.Analysis.BishopUniformLimitSequentialContinuityExact as Uniform

module OnSelectedChart
  (terms : Dirichlet.BishopDirichletTermFamily)
  (Region : BC.BishopComplex → Set)
  (bound : Tails.RegionBaselDomination terms Region)
  (chart : R.ℝ → BC.BishopComplex)
  (inside : (x : R.ℝ) → Region (chart x))
  where

  partialReal : Nat → R.ℝ → R.ℝ
  partialReal count x =
    BC.re (Dirichlet.dirichletPartial terms (chart x) count)

  partialImag : Nat → R.ℝ → R.ℝ
  partialImag count x =
    BC.im (Dirichlet.dirichletPartial terms (chart x) count)

  selectedRealLimit : R.ℝ → R.ℝ
  selectedRealLimit x =
    BC.re (Tails.regionDirichletValue
      terms Region bound (chart x) (inside x))

  selectedImagLimit : R.ℝ → R.ℝ
  selectedImagLimit x =
    BC.im (Tails.regionDirichletValue
      terms Region bound (chart x) (inside x))

  originalUniformRealApproximation :
    Uniform.UniformApproximation partialReal selectedRealLimit
  originalUniformRealApproximation k =
    Tails.baselUniformTailCutoff k ,
    (λ x →
      RP.≤-respˡ-≃
        (RP.∣x-y∣≃∣y-x∣
          (selectedRealLimit x)
          (partialReal (Tails.baselUniformTailCutoff k) x))
        (Tails.regionRealUniformLimitError
          terms Region bound k
          (chart x) (inside x)
          (Tails.baselUniformTailCutoff k)
          NatP.≤-refl))

  originalUniformImagApproximation :
    Uniform.UniformApproximation partialImag selectedImagLimit
  originalUniformImagApproximation k =
    Tails.baselUniformTailCutoff k ,
    (λ x →
      RP.≤-respˡ-≃
        (RP.∣x-y∣≃∣y-x∣
          (selectedImagLimit x)
          (partialImag (Tails.baselUniformTailCutoff k) x))
        (Tails.regionImagUniformLimitError
          terms Region bound k
          (chart x) (inside x)
          (Tails.baselUniformTailCutoff k)
          NatP.≤-refl))

  selectedDirichletRealSequentiallyContinuous :
    (∀ count → Uniform.SequentiallyContinuous (partialReal count)) →
    Uniform.SequentiallyContinuous selectedRealLimit
  selectedDirichletRealSequentiallyContinuous finiteContinuous =
    Uniform.uniformLimitSequentialContinuity
      partialReal selectedRealLimit
      finiteContinuous originalUniformRealApproximation

  selectedDirichletImagSequentiallyContinuous :
    (∀ count → Uniform.SequentiallyContinuous (partialImag count)) →
    Uniform.SequentiallyContinuous selectedImagLimit
  selectedDirichletImagSequentiallyContinuous finiteContinuous =
    Uniform.uniformLimitSequentialContinuity
      partialImag selectedImagLimit
      finiteContinuous originalUniformImagApproximation
