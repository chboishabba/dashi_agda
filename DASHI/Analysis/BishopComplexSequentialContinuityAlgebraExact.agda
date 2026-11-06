{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopComplexSequentialContinuityAlgebraExact where

------------------------------------------------------------------------
-- K04d-CONTINUITY: ACTUAL ORIGINAL BISHOP CARTESIAN OPERATIONS.
--
-- The complex carrier is the existing
-- RiemannBishopComplexAnalyticCarrierExact.BishopComplex.
-- No second complex type is introduced. Its multiplication is
-- definitionally the ordinary real/imaginary formula, and both
-- coordinates inherit sequential continuity from the pinned
-- Bishop Sequence sum/product/negation limit theorems.
--
-- This is the ring-continuity bridge needed for the selected zeta
-- and (separately) completed xi factor chain. Analytic continuity
-- of any original exp/gamma/zeta factor is NOT assumed or proved.
------------------------------------------------------------------------

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
import Real as R
import RealProperties as RP

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.BishopUniformLimitSequentialContinuityExact as U
import DASHI.Analysis.BishopSequentialContinuityRingCompilerExact as Ring
import DASHI.Analysis.BishopOriginalCompletedZetaUniformChartContinuityExact as Chart

ComplexSequentiallyContinuous :
  (R.ℝ → BC.BishopComplex) → Set
ComplexSequentiallyContinuous f =
  U.SequentiallyContinuous (λ x → BC.re (f x))
  × U.SequentiallyContinuous (λ x → BC.im (f x))

selectedProductRealFormula :
  (left right : BC.BishopComplex) →
  R._≃_
    (BC.re (BC._*C_ left right))
    (R._-_
      (R._*_ (BC.re left) (BC.re right))
      (R._*_ (BC.im left) (BC.im right)))
selectedProductRealFormula
  (BC.bishop-complex a b) (BC.bishop-complex c d) =
  RP.≃-refl

selectedProductImagFormula :
  (left right : BC.BishopComplex) →
  R._≃_
    (BC.im (BC._*C_ left right))
    (R._+_
      (R._*_ (BC.re left) (BC.im right))
      (R._*_ (BC.im left) (BC.re right)))
selectedProductImagFormula
  (BC.bishop-complex a b) (BC.bishop-complex c d) =
  RP.≃-refl

selectedComplexProductSequentiallyContinuous :
  (f g : R.ℝ → BC.BishopComplex) →
  ComplexSequentiallyContinuous f →
  ComplexSequentiallyContinuous g →
  ComplexSequentiallyContinuous
    (λ x → BC._*C_ (f x) (g x))
selectedComplexProductSequentiallyContinuous f g fCont gCont =
  Chart.pointwiseEquivalentPreservesSequentialContinuity
    (λ x → BC.re (BC._*C_ (f x) (g x)))
    (λ x →
      R._-_
        (R._*_ (BC.re (f x)) (BC.re (g x)))
        (R._*_ (BC.im (f x)) (BC.im (g x))))
    (λ x → selectedProductRealFormula (f x) (g x))
    (Ring.sequentiallyContinuousCartesianProductReal
      (λ x → BC.re (f x))
      (λ x → BC.im (f x))
      (λ x → BC.re (g x))
      (λ x → BC.im (g x))
      (proj₁ fCont) (proj₂ fCont)
      (proj₁ gCont) (proj₂ gCont))
  ,
  Chart.pointwiseEquivalentPreservesSequentialContinuity
    (λ x → BC.im (BC._*C_ (f x) (g x)))
    (λ x →
      R._+_
        (R._*_ (BC.re (f x)) (BC.im (g x)))
        (R._*_ (BC.im (f x)) (BC.re (g x))))
    (λ x → selectedProductImagFormula (f x) (g x))
    (Ring.sequentiallyContinuousCartesianProductImag
      (λ x → BC.re (f x))
      (λ x → BC.im (f x))
      (λ x → BC.re (g x))
      (λ x → BC.im (g x))
      (proj₁ fCont) (proj₂ fCont)
      (proj₁ gCont) (proj₂ gCont))
