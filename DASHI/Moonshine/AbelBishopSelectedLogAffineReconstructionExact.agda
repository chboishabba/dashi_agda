module DASHI.Moonshine.AbelBishopSelectedLogAffineReconstructionExact where

------------------------------------------------------------------------
-- ORIGINAL BISHOP-COMPLEX COORDINATE NORMALIZATION AT ANY NONZERO p.
--
-- Source-reuse: DASHI.Analysis.BishopComplexReciprocalExact already
-- constructs p^-1 and proves p * p^-1 ≈ 1 from a positive
-- norm-square witness. No second inverse package or authority.
--
-- u(p,t) = p^-1 * t, with the actual original setoid multiplication.
-- We prove p * u(p,t) ≈ t and p * (1 + u(p,t)) ≈ p+t.
--
-- The specific exponential fixed point p and its apartness witness
-- must still be independently constructed. This is algebra only;
-- it does NOT assert the Bishop exp–log inverse or Kneser existence.
------------------------------------------------------------------------

open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Moonshine.AbelBishopLogOnePlusCoefficientDominationExact as Log
import DASHI.Moonshine.AbelBishopLogOnePlusOriginalSeriesExact as Terms
import DASHI.Moonshine.AbelBishopLogFiniteComplexDerivativeExact as Finite

complexMulAssociative :
  ∀ x y z →
  Complex._≈C_
    (Algebra._*C_ x (Algebra._*C_ y z))
    (Algebra._*C_ (Algebra._*C_ x y) z)
complexMulAssociative
  (Complex.complex ar ai)
  (Complex.complex br bi)
  (Complex.complex cr ci) =
  (let open BishopP.ℝ-Solver in
   solve 6
     (λ a b c d e f →
       (a ⊗ ((c ⊗ e) ⊖ (d ⊗ f)))
       ⊖ (b ⊗ ((c ⊗ f) ⊕ (d ⊗ e)))
       ⊜
       (((a ⊗ c) ⊖ (b ⊗ d)) ⊗ e)
       ⊖ (((a ⊗ d) ⊕ (b ⊗ c)) ⊗ f))
     BishopP.≃-refl ar ai br bi cr ci)
  ,
  (let open BishopP.ℝ-Solver in
   solve 6
     (λ a b c d e f →
       (a ⊗ ((c ⊗ f) ⊕ (d ⊗ e)))
       ⊕ (b ⊗ ((c ⊗ e) ⊖ (d ⊗ f)))
       ⊜
       (((a ⊗ c) ⊖ (b ⊗ d)) ⊗ f)
       ⊕ (((a ⊗ d) ⊕ (b ⊗ c)) ⊗ e))
     BishopP.≃-refl ar ai br bi cr ci)

complexOneLeft :
  ∀ z →
  Complex._≈C_ (Algebra._*C_ Algebra.oneC z) z
complexOneLeft (Complex.complex a b) =
  (let open BishopP.ℝ-Solver in
   solve 2
     (λ x y → ((Κ 1ℚᵘ ⊗ x) ⊖ (Κ 0ℚᵘ ⊗ y)) ⊜ x)
     BishopP.≃-refl a b)
  ,
  (let open BishopP.ℝ-Solver in
   solve 2
     (λ x y → ((Κ 1ℚᵘ ⊗ y) ⊕ (Κ 0ℚᵘ ⊗ x)) ⊜ y)
     BishopP.≃-refl a b)

complexOneRight :
  ∀ z →
  Complex._≈C_ (Algebra._*C_ z Algebra.oneC) z
complexOneRight (Complex.complex a b) =
  (let open BishopP.ℝ-Solver in
   solve 2
     (λ x y → ((x ⊗ Κ 1ℚᵘ) ⊖ (y ⊗ Κ 0ℚᵘ)) ⊜ x)
     BishopP.≃-refl a b)
  ,
  (let open BishopP.ℝ-Solver in
   solve 2
     (λ x y → ((x ⊗ Κ 0ℚᵘ) ⊕ (y ⊗ Κ 1ℚᵘ)) ⊜ y)
     BishopP.≃-refl a b)

normalizedDisplacement :
  (p : Complex.BishopComplex) →
  Reciprocal.BishopComplexNonzero p →
  Complex.BishopComplex →
  Complex.BishopComplex
normalizedDisplacement p nz t =
  Algebra._*C_ (Reciprocal.reciprocalC p nz) t

originalBishopNormalizedDisplacementReconstruct :
  (p : Complex.BishopComplex) →
  (nz : Reciprocal.BishopComplexNonzero p) →
  (t : Complex.BishopComplex) →
  Complex._≈C_
    (Algebra._*C_ p (normalizedDisplacement p nz t))
    t
originalBishopNormalizedDisplacementReconstruct p nz t =
  let
    a = complexMulAssociative
      p (Reciprocal.reciprocalC p nz) t
    b = Algebra.mulCCongruent
      (Reciprocal.multiplyReciprocal p nz)
      (Complex.≈C-refl t)
    c = complexOneLeft t
  in
  (BishopP.≃-trans (proj₁ a)
    (BishopP.≃-trans (proj₁ b) (proj₁ c)))
  ,
  (BishopP.≃-trans (proj₂ a)
    (BishopP.≃-trans (proj₂ b) (proj₂ c)))

originalBishopNormalizedDisplacementAffineReconstruct :
  (p : Complex.BishopComplex) →
  (nz : Reciprocal.BishopComplexNonzero p) →
  (t : Complex.BishopComplex) →
  Complex._≈C_
    (Algebra._*C_
      p
      (Algebra._+C_
        Algebra.oneC
        (normalizedDisplacement p nz t)))
    (Algebra._+C_ p t)
originalBishopNormalizedDisplacementAffineReconstruct p nz t =
  let
    dist = Finite.complexLeftDistributive
      p Algebra.oneC (normalizedDisplacement p nz t)
    pieces = Algebra.addCCongruent
      (complexOneRight p)
      (originalBishopNormalizedDisplacementReconstruct p nz t)
  in
  BishopP.≃-trans (proj₁ dist) (proj₁ pieces)
  ,
  BishopP.≃-trans (proj₂ dist) (proj₂ pieces)


-- The original unit-disk radius for the displacement w = p^-1 * t
-- can be derived from this EXACT norm-square formula rather than
-- supplying an independent norm oracle for the normalized chart.
originalBishopNormalizedDisplacementNormSquare :
  (p : Complex.BishopComplex) →
  (nz : Reciprocal.BishopComplexNonzero p) →
  (t : Complex.BishopComplex) →
  BishopReal._≃_
    (Norm.normSqC (normalizedDisplacement p nz t))
    (BishopReal._*_
      (BishopInverse._⁻¹
        (Norm.normSqC p)
        (Reciprocal.normSquareNonzero nz))
      (Norm.normSqC t))
originalBishopNormalizedDisplacementNormSquare p nz t =
  BishopP.≃-trans
    (Norm.normSqMultiply (Reciprocal.reciprocalC p nz) t)
    (BishopP.*-congʳ
      (Reciprocal.normSquareReciprocal p nz))


-- Relative-radius compatibility is the same-object precondition:
-- normSq(t) ~= ratio^2 * normSq(p).
-- The standard Bishop reciprocal law converts this to the exact
-- norm-square certificate expected by the source logarithm series.
originalBishopNormalizedDisplacementRadius :
  (p : Complex.BishopComplex) →
  (nz : Reciprocal.BishopComplexNonzero p) →
  (t : Complex.BishopComplex) →
  (ratio : BishopReal.ℝ) →
  BishopReal._≃_
    (Norm.normSqC t)
    (BishopReal._*_ (Norm.square ratio) (Norm.normSqC p)) →
  BishopReal._≃_
    (Norm.normSqC (normalizedDisplacement p nz t))
    (Norm.square ratio)
originalBishopNormalizedDisplacementRadius p nz t ratio relativeRadius =
  let
    d = Norm.normSqC p
    inv = BishopInverse._⁻¹ d (Reciprocal.normSquareNonzero nz)
    r2 = Norm.square ratio
    rearrange :
      BishopReal._≃_
        (BishopReal._*_ inv (BishopReal._*_ r2 d))
        (BishopReal._*_ (BishopReal._*_ d inv) r2)
    rearrange =
      let open BishopP.ℝ-Solver in
      solve 3
        (λ i r pNorm →
          i ⊗ (r ⊗ pNorm)
          ⊜ (pNorm ⊗ i) ⊗ r)
        BishopP.≃-refl inv r2 d
  in
  BishopP.≃-trans
    (originalBishopNormalizedDisplacementNormSquare p nz t)
    (BishopP.≃-trans
      (BishopP.*-congˡ relativeRadius)
      (BishopP.≃-trans
        rearrange
        (BishopP.≃-trans
          (BishopP.*-congʳ
            (BishopInverse.*-inverseʳ
              d (Reciprocal.normSquareNonzero nz)))
          (BishopP.*-identityˡ r2))))

-- Direct consumer of the actual original log-series completion.
-- No caller-provided series convergence, norm-square radius of
-- normalizedDisplacement, or unrelated "log authority".
originalBishopSelectedChartLogSeries :
  (p : Complex.BishopComplex) →
  (nz : Reciprocal.BishopComplexNonzero p) →
  (t : Complex.BishopComplex) →
  (ratio : BishopReal.ℝ) →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (relativeRadius : BishopReal._≃_
    (Norm.normSqC t)
    (BishopReal._*_ (Norm.square ratio) (Norm.normSqC p))) →
  Complex.BishopComplex
originalBishopSelectedChartLogSeries p nz t ratio interval relativeRadius =
  Log.originalBishopLogOnePlusCanonicalLimitOnUnitDisk
    interval
    (originalBishopNormalizedDisplacementRadius
      p nz t ratio relativeRadius)

originalBishopSelectedChartLogSeriesConverges :
  (p : Complex.BishopComplex) →
  (nz : Reciprocal.BishopComplexNonzero p) →
  (t : Complex.BishopComplex) →
  (ratio : BishopReal.ℝ) →
  (interval : Unit.BishopUnitIntervalRatio ratio) →
  (relativeRadius : BishopReal._≃_
    (Norm.normSqC t)
    (BishopReal._*_ (Norm.square ratio) (Norm.normSqC p))) →
  Complex.ComplexSeriesConvergesTo
    (Terms.originalBishopLogOnePlusTerm
      (normalizedDisplacement p nz t))
    (originalBishopSelectedChartLogSeries p nz t ratio interval relativeRadius)
originalBishopSelectedChartLogSeriesConverges p nz t ratio interval relativeRadius =
  Log.originalBishopLogOnePlusCanonicalLimitConvergesOnUnitDisk
    interval
    (originalBishopNormalizedDisplacementRadius
      p nz t ratio relativeRadius)
