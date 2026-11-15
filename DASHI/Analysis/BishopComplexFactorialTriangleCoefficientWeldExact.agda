module DASHI.Analysis.BishopComplexFactorialTriangleCoefficientWeldExact where

------------------------------------------------------------------------
-- ORIGINAL COMPLEX FACTORIAL CAUCHY COEFFICIENT: SAME-SOURCE WELD.
--
-- The existing complex wing owner uses FOUR original real
-- Row.cauchyCoefficient owners. The finite complex binomial owner
-- uses the pair of ORIGINAL Fin(suc n) sums of complex products.
-- This module proves they are the same componentwise coefficient,
-- and consequently identifies the exact finite complex triangle.
--
-- The only finite algebra used is the original Bishop finite-series
-- difference theorem and stdlib semiring finite-sum addition.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin.Base using (toℕ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Algebra.Properties.Semiring.Sum as SemiringSum

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence
import Data.Nat.Base as Nat
import DASHI.Moonshine.AbelBishopFactorialComplexRealAxisTermsExact as Factorial

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexFactorialFiniteConvolutionExact as Conv
import DASHI.Analysis.BishopComplexFiniteSquareTriangleDifferenceExact as Wing
import DASHI.Foundations.BishopFiniteSeriesDifferenceExact as Difference
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row

module BishopSum = SemiringSum BishopP.+-*-semiring

finiteSumDifference :
  (left right : Nat → BishopReal.ℝ) →
  ∀ count →
  BishopReal._≃_
    (BishopReal._-_
      (FinSum.finSum left count)
      (FinSum.finSum right count))
    (FinSum.finSum
      (λ index → BishopReal._-_ (left index) (right index))
      count)
finiteSumDifference left right count =
  BishopP.≃-trans
    (BishopP.+-cong
      (FinSum.finSumIsSeriesOf left count)
      (BishopP.-‿cong (FinSum.finSumIsSeriesOf right count)))
    (BishopP.≃-trans
      (Difference.finiteSeriesDifference left right count)
      (BishopP.≃-symm
        (FinSum.finSumIsSeriesOf
          (λ index → BishopReal._-_ (left index) (right index))
          count)))

finiteSumAddition :
  (left right : Nat → BishopReal.ℝ) →
  ∀ count →
  BishopReal._≃_
    (BishopReal._+_
      (FinSum.finSum left count)
      (FinSum.finSum right count))
    (FinSum.finSum
      (λ index → BishopReal._+_ (left index) (right index))
      count)
finiteSumAddition left right count =
  BishopP.≃-symm
    (BishopSum.∑-distrib-+
      (λ index → left (toℕ index))
      (λ index → right (toℕ index)))

originalBishopComplexConvolutionCoefficientIsRows :
  (left right : Nat → Complex.BishopComplex) →
  ∀ degree →
  Complex._≈C_
    (Complex.complex
      (BishopReal._-_
        (Row.cauchyCoefficient
          (Complex.realTerms left) (Complex.realTerms right)
          degree)
        (Row.cauchyCoefficient
          (Complex.imagTerms left) (Complex.imagTerms right)
          degree))
      (BishopReal._+_
        (Row.cauchyCoefficient
          (Complex.realTerms left) (Complex.imagTerms right)
          degree)
        (Row.cauchyCoefficient
          (Complex.imagTerms left) (Complex.realTerms right)
          degree)))
    (Complex.complex
      (FinSum.finSum
        (λ k →
          BishopReal._-_
            (BishopReal._*_
              (Complex.re (left k))
              (Complex.re (right (degree Nat.∸ k))))
            (BishopReal._*_
              (Complex.im (left k))
              (Complex.im (right (degree Nat.∸ k)))))
        (suc degree))
      (FinSum.finSum
        (λ k →
          BishopReal._+_
            (BishopReal._*_
              (Complex.re (left k))
              (Complex.im (right (degree Nat.∸ k))))
            (BishopReal._*_
              (Complex.im (left k))
              (Complex.re (right (degree Nat.∸ k)))))
        (suc degree)))
originalBishopComplexConvolutionCoefficientIsRows
  left right degree =
  finiteSumDifference
    (λ k → BishopReal._*_
      (Complex.re (left k))
      (Complex.re (right (degree Nat.∸ k))))
    (λ k → BishopReal._*_
      (Complex.im (left k))
      (Complex.im (right (degree Nat.∸ k))))
    (suc degree)
  ,
  finiteSumAddition
    (λ k → BishopReal._*_
      (Complex.re (left k))
      (Complex.im (right (degree Nat.∸ k))))
    (λ k → BishopReal._*_
      (Complex.im (left k))
      (Complex.re (right (degree Nat.∸ k))))
    (suc degree)

-- This theorem is the actual bridge between the Cauchy coefficient used
-- in Wing.cauchyTrianglePartial and the original complex factorial
-- product coefficient in Conv, not an analogous independent definition.
originalBishopFactorialCauchyCoefficientSameRows :
  ∀ z w degree →
  Complex._≈C_
    (Complex.complex
      (BishopReal._-_
        (Row.cauchyCoefficient
          (Complex.realTerms
            (λ n → Factorial.originalBishopFactorialComplexTerm z n))
          (Complex.realTerms
            (λ n → Factorial.originalBishopFactorialComplexTerm w n))
          degree)
        (Row.cauchyCoefficient
          (Complex.imagTerms
            (λ n → Factorial.originalBishopFactorialComplexTerm z n))
          (Complex.imagTerms
            (λ n → Factorial.originalBishopFactorialComplexTerm w n))
          degree))
      (BishopReal._+_
        (Row.cauchyCoefficient
          (Complex.realTerms
            (λ n → Factorial.originalBishopFactorialComplexTerm z n))
          (Complex.imagTerms
            (λ n → Factorial.originalBishopFactorialComplexTerm w n))
          degree)
        (Row.cauchyCoefficient
          (Complex.imagTerms
            (λ n → Factorial.originalBishopFactorialComplexTerm z n))
          (Complex.realTerms
            (λ n → Factorial.originalBishopFactorialComplexTerm w n))
          degree)))
    (Conv.complexFactorialConvolutionCoefficient z w degree)
originalBishopFactorialCauchyCoefficientSameRows z w degree =
  originalBishopComplexConvolutionCoefficientIsRows
    (Factorial.originalBishopFactorialComplexTerm z)
    (Factorial.originalBishopFactorialComplexTerm w)
    degree
