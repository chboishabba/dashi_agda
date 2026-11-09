module DASHI.Moonshine.AbelBishopKoenigsTrajectoryDifferenceLimitExact where

------------------------------------------------------------------------
-- SOURCE TRAJECTORY LIMIT, NOT MERELY AN ABSTRACT INCREMENT SERIES
--
-- Given Bishop-scaled geometric component bounds on the literal
-- differences h_(n+1)-h_n, use native finite telescoping and the
-- original Bishop convergence-extensionality theorem to show
-- h_n-h_0 converges in the actual complex setoid.
--
-- The original Bishop Log still has to produce these bounds.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Product.Base using (proj₁; proj₂)
import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Moonshine.AbelBishopKoenigsGeometricAbsoluteExact as Geom
import DASHI.Moonshine.AbelBishopKoenigsFiniteTelescopingExact as Telescope
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion

originalBishopDifferenceTrajectory :
  (h : Nat → Complex.BishopComplex) →
  Nat → Complex.BishopComplex
originalBishopDifferenceTrajectory h n =
  Algebra._-C_ (h n) (h 0)

originalBishopKoenigsDifferenceLimit :
  (h : Nat → Complex.BishopComplex) →
  (constant ratio : BishopReal.ℝ) →
  Geom.OriginalBishopGeometricComponentBounds
    (Telescope.originalBishopComplexStepDifference h)
    constant ratio →
  Complex.BishopComplex
originalBishopKoenigsDifferenceLimit h constant ratio bounds =
  Geom.originalBishopKoenigsGeometricLimit
    (Telescope.originalBishopComplexStepDifference h)
    constant ratio bounds

originalBishopKoenigsDifferenceConverges :
  (h : Nat → Complex.BishopComplex) →
  (constant ratio : BishopReal.ℝ) →
  (bounds : Geom.OriginalBishopGeometricComponentBounds
    (Telescope.originalBishopComplexStepDifference h)
    constant ratio) →
  Completion.OriginalBishopPointwiseComplexConverges
    (originalBishopDifferenceTrajectory h)
    (originalBishopKoenigsDifferenceLimit h constant ratio bounds)
originalBishopKoenigsDifferenceConverges h constant ratio bounds =
  Completion.original-bishop-pointwise-complex-converges
    (BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ n {{_}} →
        proj₁ (Telescope.originalBishopKoenigsPrefixSameSource h n))
      (Completion.realConverges prefixConverges))
    (BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ n {{_}} →
        proj₂ (Telescope.originalBishopKoenigsPrefixSameSource h n))
      (Completion.imaginaryConverges prefixConverges))
  where
    prefixConverges =
      Geom.originalBishopKoenigsGeometricLimitConverges
        (Telescope.originalBishopComplexStepDifference h)
        constant ratio bounds
