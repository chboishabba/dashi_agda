module DASHI.Analysis.BishopComplexExpFactEqualsNativeExpExact where

------------------------------------------------------------------------
-- P1 CAPSTONE: ORIGINAL COMPLEX FACTORIAL SERIES = NATIVE expC.
--
-- For arbitrary Bishop-real x,y and the repository's configured
-- BishopSetoidComplexTranscendentals T, the *literal* all-degree
-- factorial series of the exact Cartesian input (x,y) converges
-- in both original Bishop coordinates to native expC T (x+iy).
--
-- This combines, without any assumed complex product theorem:
--  (1) original real/imaginary factorial convergence on every cutoff;
--  (2) finite original Bishop-complex rectangle product;
--  (3) original four-wing absolute majorants and vanishing moduli;
--  (4) original rectangle -> Cauchy triangle limit transport;
--  (5) stdlib complex semiring/binomial power theorem on SAME carrier;
--  (6) original reciprocal-factorial binomial finite coefficient;
--  (7) exact finite coefficient-to-Cauchy triangle weld;
--  (8) original source-valued finite-to-infinite convergence transport.
--
-- This is SOURCE-WRITTEN, NOT AGDA KERNEL VERIFIED.
-- No uninhabited closing leaf or postulate is imported.
------------------------------------------------------------------------

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
import Real as BishopReal
import Sequence as BishopSequence
import RealProperties as BishopP
open import Agda.Builtin.Nat using (Nat)
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexFiniteRectangleProductExact as Rectangle
import DASHI.Analysis.BishopComplexFiniteSquareTriangleDifferenceExact as Triangle
import DASHI.Analysis.BishopComplexTriangleTailsVanishingExact as Tail
import DASHI.Analysis.BishopComplexCauchyTriangleLimitTransportExact as Transport
import DASHI.Foundations.BishopFinSumSeriesBridgeExact as FinSum
import DASHI.Moonshine.AbelBishopFactorialComplexImaginaryAxisTwoStepExact as Axis
import DASHI.Moonshine.AbelBishopFactorialComplexExpDiskExact as Disk
import DASHI.Analysis.BishopComplexFiniteBinomialTheoremExact as FiniteBinomial

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopSetoidComplexExact as Cartesian
import DASHI.Analysis.BishopComplexExpFactFiniteBinomialReductionExact as Reduction
import DASHI.Analysis.BishopComplexFactorialBinomialCapstoneExact as Binomial
import DASHI.Moonshine.AbelBishopFactorialComplexRealAxisTermsExact as Factorial
import DASHI.Moonshine.AbelBishopOriginalComplexCarrierWeldExact as Weld

originalBishopExpFactEqualsNativeExp :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ (x y : BishopReal.ℝ) →
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (Complex.realTerms
        (Factorial.originalBishopFactorialComplexTerm
          (Complex.complex x y))))
    (Complex.re
      (Weld.originalBishopExpOnSeries T (Complex.complex x y)))
  ×
  BishopSequence._ConvergesTo_
    (BishopSequence.SeriesOf
      (Complex.imagTerms
        (Factorial.originalBishopFactorialComplexTerm
          (Complex.complex x y))))
    (Complex.im
      (Weld.originalBishopExpOnSeries T (Complex.complex x y)))
originalBishopExpFactEqualsNativeExp T x y =
  Reduction.originalBishopFactorialSeriesEqualsNativeExpFromFiniteBinomial
    T x y
    (Binomial.originalBishopFiniteComplexBinomialLeafInhabited x y)


-- Canonical complex-series consumer on exactly the same original
-- factor terms, not just a pair of scalar convergence facts.
originalBishopExpFactComplexSeriesConvergesToNativeExp :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ (x y : BishopReal.ℝ) →
  Complex.ComplexSeriesConvergesTo
    (Factorial.originalBishopFactorialComplexTerm
      (Complex.complex x y))
    (Weld.originalBishopExpOnSeries T (Complex.complex x y))
originalBishopExpFactComplexSeriesConvergesToNativeExp T x y =
  let components = originalBishopExpFactEqualsNativeExp T x y
  in
  Complex.complex-series-converges-to
    (proj₁ components)
    (proj₂ components)


------------------------------------------------------------------------
-- Original imaginary-axis multiplication. Source-written, not kernel
-- accepted. The actual finite convolution, rectangle and wing owners
-- are reused, as are the original Bishop scalar convergence operations.
-- Attribution: Bishop & Bridges, Constructive Analysis (1985);
-- existing original vendored Bishop carrier and preceding DASHI proofs.
------------------------------------------------------------------------

imaginaryPairCoefficient :
  ∀ x y n →
  Complex._≈C_
    (Algebra.scaleC (Disk.factorialCoefficient n)
      (Algebra.powC (Algebra._+C_ (Axis.imaginaryAxis x)
        (Axis.imaginaryAxis y)) n))
    (Factorial.originalBishopFactorialComplexTerm
      (Axis.imaginaryAxis (BishopReal._+_ x y)) n)
imaginaryPairCoefficient x y n =
  Algebra.scaleCCongruent
    (Algebra.powCCongruent
      (BishopP.+-identityʳ BishopReal.0ℝ , BishopP.≃-refl) n)
    (Disk.factorialCoefficient n)

originalBishopImaginaryPairPrefix :
  ∀ x y n →
  Complex._≈C_
    (Triangle.cauchyTrianglePartial
      (Tail.factorialImaginaryStream x)
      (Tail.factorialImaginaryStream y) n)
    (Rectangle.finiteComplexPartial
      (Tail.factorialImaginaryStream (BishopReal._+_ x y)) n)
originalBishopImaginaryPairPrefix x y n =
  let
    z = Axis.imaginaryAxis x
    w = Axis.imaginaryAxis y
    sameDegree = λ k → FiniteBinomial.complexTrans
      (Binomial.originalBishopComplexFactorialFiniteBinomial z w k)
      (imaginaryPairCoefficient x y k)
    samePrefix =
      Reduction.originalBishopComplexFactorialTrianglePrefixSameConvolution z w n
  in
  (BishopP.≃-trans (proj₁ samePrefix)
    (BishopP.≃-trans
      (Reduction.finiteSumPointwiseEquivalent
        (λ k → proj₁ (sameDegree k)) n)
      (FinSum.finSumIsSeriesOf
        (Complex.realTerms
          (Tail.factorialImaginaryStream (BishopReal._+_ x y))) n)))
  ,
  (BishopP.≃-trans (proj₂ samePrefix)
    (BishopP.≃-trans
      (Reduction.finiteSumPointwiseEquivalent
        (λ k → proj₂ (sameDegree k)) n)
      (FinSum.finSumIsSeriesOf
        (Complex.imagTerms
          (Tail.factorialImaginaryStream (BishopReal._+_ x y))) n)))

originalBishopImaginaryExpProductOnSeries :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ x y →
  Complex._≈C_
    (Weld.originalBishopExpOnSeries T
      (Axis.imaginaryAxis (BishopReal._+_ x y)))
    (Algebra._*C_
      (Weld.originalBishopExpOnSeries T (Axis.imaginaryAxis x))
      (Weld.originalBishopExpOnSeries T (Axis.imaginaryAxis y)))
originalBishopImaginaryExpProductOnSeries T x y =
  let
    left = Tail.factorialImaginaryStream x
    right = Tail.factorialImaginaryStream y
    z = Weld.originalBishopExpOnSeries T (Axis.imaginaryAxis x)
    w = Weld.originalBishopExpOnSeries T (Axis.imaginaryAxis y)
    target = Algebra._*C_ z w
    xLimits = originalBishopExpFactEqualsNativeExp T BishopReal.0ℝ x
    yLimits = originalBishopExpFactEqualsNativeExp T BishopReal.0ℝ y
    sumLimits = originalBishopExpFactEqualsNativeExp T
      BishopReal.0ℝ (BishopReal._+_ x y)
    ac = BishopSequence.xₙyₙ→x₀y₀
      (Complex.re z , proj₁ xLimits) (Complex.re w , proj₁ yLimits)
    bd = BishopSequence.xₙyₙ→x₀y₀
      (Complex.im z , proj₂ xLimits) (Complex.im w , proj₂ yLimits)
    ad = BishopSequence.xₙyₙ→x₀y₀
      (Complex.re z , proj₁ xLimits) (Complex.im w , proj₂ yLimits)
    bc = BishopSequence.xₙyₙ→x₀y₀
      (Complex.im z , proj₂ xLimits) (Complex.re w , proj₁ yLimits)
    reProduct = BishopSequence.xₙ+yₙ→x₀+y₀
      (BishopReal._*_ (Complex.re z) (Complex.re w) , ac)
      (BishopReal.-_ (BishopReal._*_ (Complex.im z) (Complex.im w)) ,
        BishopSequence.-xₙ→-x₀
          (BishopReal._*_ (Complex.im z) (Complex.im w) , bd))
    imProduct = BishopSequence.xₙ+yₙ→x₀+y₀
      (BishopReal._*_ (Complex.re z) (Complex.im w) , ad)
      (BishopReal._*_ (Complex.im z) (Complex.re w) , bc)
    reRectangle = BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ n → BishopP.≃-symm
        (proj₁ (Rectangle.originalBishopComplexSquareRectangleProduct
          left right n)))
      (Complex.re target , reProduct)
    imRectangle = BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ n → BishopP.≃-symm
        (proj₂ (Rectangle.originalBishopComplexSquareRectangleProduct
          left right n)))
      (Complex.im target , imProduct)
    triangleLimits =
      Transport.originalBishopComplexTriangleLimitTransport
        left right target reRectangle imRectangle
        (Tail.originalBishopImaginaryPairWingRealConvergesZero x y)
        (Tail.originalBishopImaginaryPairWingImagConvergesZero x y)
    sumTarget = Weld.originalBishopExpOnSeries T
      (Axis.imaginaryAxis (BishopReal._+_ x y))
    reSumTriangle = BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ n → BishopP.≃-symm (proj₁ (originalBishopImaginaryPairPrefix x y n)))
      (Complex.re sumTarget , proj₁ sumLimits)
    imSumTriangle = BishopSequence.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ n → BishopP.≃-symm (proj₂ (originalBishopImaginaryPairPrefix x y n)))
      (Complex.im sumTarget , proj₂ sumLimits)
  in
  BishopSequence.uniqueness-of-limits reSumTriangle (proj₁ triangleLimits)
  ,
  BishopSequence.uniqueness-of-limits imSumTriangle (proj₂ triangleLimits)

originalBishopImaginaryExpMultiplicative :
  (T : Cartesian.BishopSetoidComplexTranscendentals) →
  ∀ x y →
  Cartesian._≈C_
    (Cartesian.expC T
      (Cartesian.complex BishopReal.0ℝ (BishopReal._+_ x y)))
    (Cartesian._*C_
      (Cartesian.expC T (Cartesian.complex BishopReal.0ℝ x))
      (Cartesian.expC T (Cartesian.complex BishopReal.0ℝ y)))
originalBishopImaginaryExpMultiplicative T x y =
  Weld.originalSeriesEquivalenceToExp
    (originalBishopImaginaryExpProductOnSeries T x y)
