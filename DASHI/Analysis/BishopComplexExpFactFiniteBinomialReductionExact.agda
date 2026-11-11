module DASHI.Analysis.BishopComplexExpFactFiniteBinomialReductionExact where

------------------------------------------------------------------------
-- ALL-ARGUMENT expFact -> NATIVE expC: EXACT REMAINING BINOMIAL CUT.
--
-- This is a conditional closing reduction, not a completed equality:
-- the ONLY explicit hypothesis is the all-degree original finite
-- complex coefficient binomial identity, written on the exact source
-- carrier. Everything analytic is supplied by the actual source
-- proof of convergence of the Cauchy triangle to native expC.
--
-- No new functional/analytic authority is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (toℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
import Algebra.Properties.Semiring.Sum as SemiringSum

import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Analysis.BishopComplexFactorialFiniteConvolutionExact as Conv
import DASHI.Analysis.BishopComplexFactorialTriangleCoefficientWeldExact as WeldCoefficient
import DASHI.Analysis.BishopComplexFiniteSquareTriangleDifferenceExact as Triangle
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Analysis.BishopComplexFactorialTriangleNativeExpExact as TriangleLimit
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
import DASHI.Moonshine.AbelBishopFactorialComplexRealAxisTermsExact as Factorial
import DASHI.Moonshine.AbelBishopFactorialComplexImaginaryAxisTwoStepExact as Axis
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Native

module BishopSum = SemiringSum BishopP.+-*-semiring

finiteSumPointwiseEquivalent :
  ∀ {left right : Nat → BishopReal.ℝ} →
  (∀ n → BishopReal._≃_ (left n) (right n)) →
  ∀ count →
  BishopReal._≃_
    (FinSum.finSum left count)
    (FinSum.finSum right count)
finiteSumPointwiseEquivalent pointwise count =
  BishopSum.sum-cong-≋ (λ index → pointwise (toℕ index))

originalBishopComplexFactorialTrianglePrefixSameConvolution :
  ∀ (z w : Complex.BishopComplex) count →
  Complex._≈C_
    (Triangle.cauchyTrianglePartial
      (Factorial.originalBishopFactorialComplexTerm z)
      (Factorial.originalBishopFactorialComplexTerm w)
      count)
    (Complex.complex
      (FinSum.finSum
        (λ n → Complex.re
          (Conv.complexFactorialConvolutionCoefficient z w n))
        count)
      (FinSum.finSum
        (λ n → Complex.im
          (Conv.complexFactorialConvolutionCoefficient z w n))
        count))
originalBishopComplexFactorialTrianglePrefixSameConvolution
  z w count =
  let
    left = Factorial.originalBishopFactorialComplexTerm z
    right = Factorial.originalBishopFactorialComplexTerm w
    a = Complex.realTerms left
    b = Complex.imagTerms left
    c = Complex.realTerms right
    d = Complex.imagTerms right
    finiteReal =
      WeldCoefficient.finiteSumDifference
        (Row.cauchyCoefficient a c)
        (Row.cauchyCoefficient b d)
        count
    finiteImag =
      WeldCoefficient.finiteSumAddition
        (Row.cauchyCoefficient a d)
        (Row.cauchyCoefficient b c)
        count
  in
  (BishopP.≃-trans finiteReal
    (finiteSumPointwiseEquivalent
      (λ n →
        proj₁
          (WeldCoefficient.originalBishopFactorialCauchyCoefficientSameRows
            z w n))
      count))
  ,
  (BishopP.≃-trans finiteImag
    (finiteSumPointwiseEquivalent
      (λ n →
        proj₂
          (WeldCoefficient.originalBishopFactorialCauchyCoefficientSameRows
            z w n))
      count))

record OriginalBishopFiniteComplexBinomialLeaf
    (x y : BishopReal.ℝ) : Set where
  field
    degreeCoefficient :
      ∀ n →
      Complex._≈C_
        (Conv.complexFactorialConvolutionCoefficient
          (Factorial.realAxis x) (Axis.imaginaryAxis y) n)
        (Factorial.originalBishopFactorialComplexTerm
          (Complex.complex x y) n)

open OriginalBishopFiniteComplexBinomialLeaf public

-- The leaf above is not supplied by a constructor or postulate.
-- Its inhabitant must come from the original complex ring's
-- finite binomial theorem. This theorem merely makes the completed
-- analytic chain available immediately when that proof arrives.
originalBishopFactorialSeriesEqualsNativeExpFromFiniteBinomial :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ x y →
  OriginalBishopFiniteComplexBinomialLeaf x y →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (Complex.realTerms
        (Factorial.originalBishopFactorialComplexTerm
          (Complex.complex x y))))
    (Complex.re
      (Native.originalBishopExpOnSeries T (Complex.complex x y)))
  ×
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (Complex.imagTerms
        (Factorial.originalBishopFactorialComplexTerm
          (Complex.complex x y))))
    (Complex.im
      (Native.originalBishopExpOnSeries T (Complex.complex x y)))
originalBishopFactorialSeriesEqualsNativeExpFromFiniteBinomial
  T x y finiteBinomial =
  let
    z = Factorial.realAxis x
    w = Axis.imaginaryAxis y
    triangleLimits =
      TriangleLimit.originalBishopFactorialTriangleConvergesToNativeExp
        T x y

    originalRealPrefix :
      ∀ n →
      BishopReal._≃_
        (Complex.re (Triangle.cauchyTrianglePartial
          (Factorial.originalBishopFactorialComplexTerm z)
          (Factorial.originalBishopFactorialComplexTerm w) n))
        (BishopSequence.SeriesOf
          (Complex.realTerms
            (Factorial.originalBishopFactorialComplexTerm
              (Complex.complex x y))) n)
    originalRealPrefix n =
      BishopP.≃-trans
        (proj₁
          (originalBishopComplexFactorialTrianglePrefixSameConvolution
            z w n))
        (BishopP.≃-trans
          (finiteSumPointwiseEquivalent
            (λ degree → proj₁ (degreeCoefficient finiteBinomial degree))
            n)
          (FinSum.finSumIsSeriesOf
            (Complex.realTerms
              (Factorial.originalBishopFactorialComplexTerm
                (Complex.complex x y)))
            n))

    originalImagPrefix :
      ∀ n →
      BishopReal._≃_
        (Complex.im (Triangle.cauchyTrianglePartial
          (Factorial.originalBishopFactorialComplexTerm z)
          (Factorial.originalBishopFactorialComplexTerm w) n))
        (BishopSequence.SeriesOf
          (Complex.imagTerms
            (Factorial.originalBishopFactorialComplexTerm
              (Complex.complex x y))) n)
    originalImagPrefix n =
      BishopP.≃-trans
        (proj₂
          (originalBishopComplexFactorialTrianglePrefixSameConvolution
            z w n))
        (BishopP.≃-trans
          (finiteSumPointwiseEquivalent
            (λ degree → proj₂ (degreeCoefficient finiteBinomial degree))
            n)
          (FinSum.finSumIsSeriesOf
            (Complex.imagTerms
              (Factorial.originalBishopFactorialComplexTerm
                (Complex.complex x y)))
            n))
  in
  (BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ n → originalRealPrefix n)
    (Complex.re
      (Native.originalBishopExpOnSeries T (Complex.complex x y))
    , proj₁ triangleLimits))
  ,
  (BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
    (λ n → originalImagPrefix n)
    (Complex.im
      (Native.originalBishopExpOnSeries T (Complex.complex x y))
    , proj₂ triangleLimits))
