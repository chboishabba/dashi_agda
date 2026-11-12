module DASHI.Moonshine.AbelBishopSelectedLogQuadraticRemainderWeldExact where

------------------------------------------------------------------------
-- SAME ORIGINAL BISHOP SOURCE:
-- selected local log germ - linear term = canonical quadratic log tail.
--
-- Fix p with an ACTUAL BishopComplexNonzero witness and an admissible
-- normalized relative-radius witness for t=(w-p). Define
--
--  u = p^-1 * t,
--  selectedGerm = p + sourceLogOnePlus(u).
--
-- This module proves on the original Bishop complex SETOID:
--
--  ((selectedGerm - p) - u)
--        ~= sourceLogOnePlus(u) - u
--        = the canonical convergent shifted degree>=2 logarithm tail.
--
-- No principal-branch identity, fixed-point existence, or quadratic
-- numerical norm estimate is asserted. Those are separate analytic
-- constructors, not fields silently discharged by this weld.
------------------------------------------------------------------------

open import Data.Product.Base using (_,_; proj₁; proj₂)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.AbelBishopSelectedLogAffineReconstructionExact as Affine
import DASHI.Moonshine.AbelBishopLogQuadraticFiniteTailExact as Finite
import DASHI.Moonshine.AbelBishopLogQuadraticSeriesLimitExact as Tail

selectedBishopRelativeLogQuadraticRemainder :
  (p : Complex.BishopComplex) →
  (nz : Reciprocal.BishopComplexNonzero p) →
  (t : Complex.BishopComplex) →
  (ratio : BishopReal.ℝ) →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (relativeRadius : BishopReal._≃_
    (Norm.normSqC t)
    (BishopReal._*_
      (Norm.square ratio)
      (Norm.normSqC p))) →
  Complex.BishopComplex
selectedBishopRelativeLogQuadraticRemainder
  p nz t ratio interval relativeRadius =
  Tail.logQuadraticCanonicalRemainder
    interval
    (Affine.originalBishopNormalizedDisplacementRadius
      p nz t ratio relativeRadius)

selectedBishopLogGermRemainderIsCanonicalTail :
  ∀ p (nz : Reciprocal.BishopComplexNonzero p)
    t ratio
    (interval : Unit.BishopUnitIntervalRatio ratio)
    (relativeRadius : BishopReal._≃_
      (Norm.normSqC t)
      (BishopReal._*_
        (Norm.square ratio)
        (Norm.normSqC p))) →
  Complex._≈C_
    (Algebra._-C_
      (Algebra._-C_
        (Affine.originalBishopSelectedLocalLogGerm
          p nz t ratio interval relativeRadius)
        p)
      (Affine.normalizedDisplacement p nz t))
    (selectedBishopRelativeLogQuadraticRemainder
      p nz t ratio interval relativeRadius)
selectedBishopLogGermRemainderIsCanonicalTail
  (Complex.complex pr pi) nz t ratio interval relativeRadius =
  let
    p = Complex.complex pr pi
    u = Affine.normalizedDisplacement p nz t
    logarithm =
      Affine.originalBishopSelectedChartLogSeries
        p nz t ratio interval relativeRadius
  in
  (let open BishopP.ℝ-Solver in
    solve 3
      (λ p l u′ →
        ((p ⊕ l) ⊖ p) ⊖ u′ ⊜ l ⊖ u′)
      BishopP.≃-refl
      pr (Complex.re logarithm) (Complex.re u))
  ,
  (let open BishopP.ℝ-Solver in
    solve 3
      (λ p l u′ →
        ((p ⊕ l) ⊖ p) ⊖ u′ ⊜ l ⊖ u′)
      BishopP.≃-refl
      pi (Complex.im logarithm) (Complex.im u))

selectedBishopLogGermQuadraticTailConverges :
  ∀ p (nz : Reciprocal.BishopComplexNonzero p)
    t ratio
    (interval : Unit.BishopUnitIntervalRatio ratio)
    (relativeRadius : BishopReal._≃_
      (Norm.normSqC t)
      (BishopReal._*_
        (Norm.square ratio)
        (Norm.normSqC p))) →
  Completion.OriginalBishopPointwiseComplexConverges
    (Finite.originalBishopLogQuadraticTailPrefix
      (Affine.normalizedDisplacement p nz t))
    (selectedBishopRelativeLogQuadraticRemainder
      p nz t ratio interval relativeRadius)
selectedBishopLogGermQuadraticTailConverges
  p nz t ratio interval relativeRadius =
  Tail.originalBishopLogQuadraticTailConverges
    interval
    (Affine.originalBishopNormalizedDisplacementRadius
      p nz t ratio relativeRadius)
