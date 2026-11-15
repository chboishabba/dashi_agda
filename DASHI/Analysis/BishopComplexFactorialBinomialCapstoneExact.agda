module DASHI.Analysis.BishopComplexFactorialBinomialCapstoneExact where

------------------------------------------------------------------------
-- ACTUAL FINITE COMPLEX FACTORIAL BINOMIAL CAPSTONE, ALL DEGREES.
--
-- No missing input record, postulate, or parallel complex carrier:
--   sum_(k=0)^n (z^k/k!) * (w^(n-k)/(n-k)!)
--              ~= (z+w)^n/n!
--
-- The proof composes the exact original Bishop complex semiring,
-- the stdlib finite binomial theorem, the original rational
-- inverse-factorial coefficient theorem and semiring finite sums.
-- The specialization to x+iy inhabits the final closing reduction.
--
-- Kernel acceptance remains separate from source-writing.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin.Base using (Fin; toℕ)
import Data.Nat.Base as ℕ
import Data.Nat.Combinatorics as Comb
open import Data.Product.Base using (_,_; proj₁; proj₂)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexFactorialBinomialSummandExact as Summand
import DASHI.Analysis.BishopComplexFactorialFiniteConvolutionExact as Conv
import DASHI.Analysis.BishopComplexFiniteBinomialTheoremExact as Binomial
import DASHI.Analysis.BishopComplexFiniteBinomialScaleExact as Scale
import DASHI.Analysis.BishopComplexFiniteBinomialExpansionBridgeExact as Expansion
import DASHI.Analysis.BishopComplexExpFactFiniteBinomialReductionExact as Reduction
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as NatReal
import DASHI.Moonshine.AbelBishopFactorialComplexRealAxisTermsExact as Factorial
import DASHI.Moonshine.AbelBishopFactorialComplexImaginaryAxisTwoStepExact as Axis

coeff : Nat → BishopReal.ℝ
coeff n = Exp.embed (Exp.inverseFactorial n)

originalBishopComplexBinomialSummandCommonCoefficient :
  ∀ z w n (index : Fin (suc n)) →
  Complex._≈C_
    (Conv.complexBinomialConvolutionTerm z w n (toℕ index))
    (Algebra.scaleC (coeff n)
      (Binomial.OriginalComplexBinomial.binomialTerm
        z w n index))
originalBishopComplexBinomialSummandCommonCoefficient
  z w n index =
  let
    k = toℕ index
    m = n ℕ.∸ k
    choose = NatReal.natReal (n Comb.C k)
    nativePowers =
      Algebra._*C_ (Algebra.powC z k) (Algebra.powC w m)
    backwards =
      Binomial.complexTrans
        (Algebra.scaleCCongruent
          (Scale.originalBishopComplexBinomialTermIsNative
            z w n index)
          (coeff n))
        (Binomial.complexTrans
          (Scale.originalBishopComplexNestedScale
            (coeff n) choose nativePowers)
          (Summand.originalBishopComplexScaleCongruent
            (BishopP.*-comm (coeff n) choose)
            nativePowers))
  in
  Binomial.complexSym backwards

originalBishopBinomialCoefficientIsScaledExpansion :
  ∀ z w n →
  Complex._≈C_
    (Conv.complexBinomialConvolutionCoefficient z w n)
    (Algebra.scaleC (coeff n)
      (Binomial.OriginalComplexBinomial.binomialExpansion
        z w n))
originalBishopBinomialCoefficientIsScaledExpansion z w n =
  let
    open Expansion.OriginalRealSum
    terms = Binomial.OriginalComplexBinomial.binomialTerm z w n
    expansionCoordinates =
      Expansion.originalBishopStdlibComplexBinomialExpansionCoordinates
        z w n

    realSummands =
      sum-cong-≋
        (λ index →
          proj₁ (originalBishopComplexBinomialSummandCommonCoefficient
            z w n index))
    realFactor =
      BishopP.≃-symm
        (*-distribˡ-sum (coeff n)
          (λ index → Complex.re (terms index)))
    realTarget =
      BishopP.*-congˡ
        (BishopP.≃-symm (proj₁ expansionCoordinates))

    imaginarySummands =
      sum-cong-≋
        (λ index →
          proj₂ (originalBishopComplexBinomialSummandCommonCoefficient
            z w n index))
    imaginaryFactor =
      BishopP.≃-symm
        (*-distribˡ-sum (coeff n)
          (λ index → Complex.im (terms index)))
    imaginaryTarget =
      BishopP.*-congˡ
        (BishopP.≃-symm (proj₂ expansionCoordinates))
  in
  (BishopP.≃-trans realSummands
    (BishopP.≃-trans realFactor realTarget))
  ,
  (BishopP.≃-trans imaginarySummands
    (BishopP.≃-trans imaginaryFactor imaginaryTarget))

originalBishopComplexFactorialFiniteBinomial :
  ∀ z w n →
  Complex._≈C_
    (Conv.complexFactorialConvolutionCoefficient z w n)
    (Factorial.originalBishopFactorialComplexTerm
      (Algebra._+C_ z w) n)
originalBishopComplexFactorialFiniteBinomial z w n =
  Binomial.complexTrans
    (Conv.originalBishopComplexFiniteFactorialCoefficientIsBinomial
      z w n)
    (Binomial.complexTrans
      (originalBishopBinomialCoefficientIsScaledExpansion z w n)
      (Algebra.scaleCCongruent
        (Binomial.complexSym
          (Binomial.originalBishopComplexFiniteBinomialPower
            z w n))
        (coeff n)))

originalBishopRealPlusImaginaryAxisIsCartesian :
  ∀ x y →
  Complex._≈C_
    (Algebra._+C_ (Factorial.realAxis x) (Axis.imaginaryAxis y))
    (Complex.complex x y)
originalBishopRealPlusImaginaryAxisIsCartesian x y =
  BishopP.+-identityʳ x
  ,
  BishopP.+-identityˡ y

originalBishopFiniteComplexBinomialLeafInhabited :
  ∀ x y →
  Reduction.OriginalBishopFiniteComplexBinomialLeaf x y
originalBishopFiniteComplexBinomialLeafInhabited x y =
  record
    { degreeCoefficient = λ n →
        Binomial.complexTrans
          (originalBishopComplexFactorialFiniteBinomial
            (Factorial.realAxis x)
            (Axis.imaginaryAxis y)
            n)
          (Algebra.scaleCCongruent
            (Algebra.powCCongruent n
              (originalBishopRealPlusImaginaryAxisIsCartesian x y))
            (coeff n))
    }
