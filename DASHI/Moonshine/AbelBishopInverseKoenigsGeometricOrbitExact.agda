module DASHI.Moonshine.AbelBishopInverseKoenigsGeometricOrbitExact where

------------------------------------------------------------------------
-- SOURCE INVERSE-KOENIGS GEOMETRIC-INCREMENT COMPLETION.
--
-- Take the LITERAL source inverse-log orbit
--     h_n(z) = p^n *C (g^n(z) -C p).
--
-- If actual signed differences h_(n+1)-h_n satisfy the original
-- Bishop Geom.OriginalBishopGeometricComponentBounds, the existing
-- increment-series completion constructs their canonical Bishop
-- limit d. From h_n - h_0 -> d, prove h_n -> d + h_0.
--
-- This pays the previous generic "source trajectory is Cauchy"
-- conversion with the exact original increment owner.
-- The geometric bounds remain an explicit, genuine analytic input
-- to be proved from a selected g=Log branch.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexConstantMultiplicationConvergenceExact as Multiply
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.AbelBishopKoenigsGeometricAbsoluteExact as Geom
import DASHI.Moonshine.AbelBishopKoenigsFiniteTelescopingExact as Telescope
import DASHI.Moonshine.AbelBishopKoenigsTrajectoryDifferenceLimitExact as Difference
import DASHI.Moonshine.AbelBishopInverseKoenigsFiniteOrbitExact as Orbit

originalBishopGeometricOrbitLimit :
  (h : Nat → Complex.BishopComplex) →
  (constant ratio : BishopReal.ℝ) →
  Geom.OriginalBishopGeometricComponentBounds
    (Telescope.originalBishopComplexStepDifference h)
    constant ratio →
  Complex.BishopComplex
originalBishopGeometricOrbitLimit h constant ratio bounds =
  Algebra._+C_
    (Difference.originalBishopKoenigsDifferenceLimit
      h constant ratio bounds)
    (h zero)

originalBishopGeometricOrbitConverges :
  (h : Nat → Complex.BishopComplex) →
  (constant ratio : BishopReal.ℝ) →
  (bounds : Geom.OriginalBishopGeometricComponentBounds
    (Telescope.originalBishopComplexStepDifference h)
    constant ratio) →
  Completion.OriginalBishopPointwiseComplexConverges h
    (originalBishopGeometricOrbitLimit h constant ratio bounds)
originalBishopGeometricOrbitConverges h constant ratio bounds =
  let
    d = Difference.originalBishopKoenigsDifferenceLimit
      h constant ratio bounds
    h0 = h zero
    diffConverges =
      Difference.originalBishopKoenigsDifferenceConverges
        h constant ratio bounds

    realSum =
      BishopSequence.xₙ+yₙ→x₀+y₀
        (Complex.re d , Completion.realConverges diffConverges)
        (Complex.re h0 ,
          Multiply.originalBishopConstantSequenceConverges
            (Complex.re h0))
    imaginarySum =
      BishopSequence.xₙ+yₙ→x₀+y₀
        (Complex.im d , Completion.imaginaryConverges diffConverges)
        (Complex.im h0 ,
          Multiply.originalBishopConstantSequenceConverges
            (Complex.im h0))
  in
  Completion.original-bishop-pointwise-complex-converges
    (BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ n →
        let open BishopP.ℝ-Solver in
        solve 2
          (λ current first →
            (current ⊖ first) ⊕ first ⊜ current)
          BishopP.≃-refl
          (Complex.re (h n))
          (Complex.re h0))
      (Complex.re (originalBishopGeometricOrbitLimit
        h constant ratio bounds) ,
        realSum))
    (BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ n →
        let open BishopP.ℝ-Solver in
        solve 2
          (λ current first →
            (current ⊖ first) ⊕ first ⊜ current)
          BishopP.≃-refl
          (Complex.im (h n))
          (Complex.im h0))
      (Complex.im (originalBishopGeometricOrbitLimit
        h constant ratio bounds) ,
        imaginarySum))

originalBishopInverseKoenigsGeometricLimit :
  (p : Complex.BishopComplex) →
  (g : Complex.BishopComplex → Complex.BishopComplex) →
  (z : Complex.BishopComplex) →
  (constant ratio : BishopReal.ℝ) →
  Geom.OriginalBishopGeometricComponentBounds
    (Telescope.originalBishopComplexStepDifference
      (λ n → Orbit.inverseKoenigsPrefix p g n z))
    constant ratio →
  Complex.BishopComplex
originalBishopInverseKoenigsGeometricLimit p g z constant ratio bounds =
  originalBishopGeometricOrbitLimit
    (λ n → Orbit.inverseKoenigsPrefix p g n z)
    constant ratio bounds

originalBishopInverseKoenigsGeometricConverges :
  (p : Complex.BishopComplex) →
  (g : Complex.BishopComplex → Complex.BishopComplex) →
  (z : Complex.BishopComplex) →
  (constant ratio : BishopReal.ℝ) →
  (bounds : Geom.OriginalBishopGeometricComponentBounds
    (Telescope.originalBishopComplexStepDifference
      (λ n → Orbit.inverseKoenigsPrefix p g n z))
    constant ratio) →
  Completion.OriginalBishopPointwiseComplexConverges
    (λ n → Orbit.inverseKoenigsPrefix p g n z)
    (originalBishopInverseKoenigsGeometricLimit
      p g z constant ratio bounds)
originalBishopInverseKoenigsGeometricConverges
  p g z constant ratio bounds =
  originalBishopGeometricOrbitConverges
    (λ n → Orbit.inverseKoenigsPrefix p g n z)
    constant ratio bounds
