module DASHI.Analysis.BishopComplexFactorialFiniteConvolutionExact where

------------------------------------------------------------------------
-- FINITE DEGREE-n COMPLEX FACTORIAL CONVOLUTION -> BINOMIAL SUM.
--
-- The first side is the Fin(suc n) sum of the LITERAL original
-- factorial complex source terms. The second side is the sum of
-- NAT choose(n,k) times the original two complex powers, with a
-- common inverse n! factor. No new complex-series authority.
--
-- This is the missing finite sum lift of the source coefficient
-- theorem in BishopComplexFactorialBinomialSummandExact.
--
-- Still unpaid: the actual complex binomial expansion identifying
-- the binomial sum with (z+w)^n/n!, and infinite limit transport.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin.Base using (toℕ)
import Data.Fin.Properties as FinP
import Data.Nat.Base as ℕ
import Data.Nat.Combinatorics as Comb
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Algebra.Properties.Semiring.Sum as SemiringSum

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexFactorialBinomialSummandExact as Summand
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as NatReal
import DASHI.Moonshine.AbelBishopFactorialComplexRealAxisTermsExact as Factorial

module BishopSum = SemiringSum BishopP.+-*-semiring

complexFactorialConvolutionTerm :
  Complex.BishopComplex → Complex.BishopComplex →
  Nat → Nat → Complex.BishopComplex
complexFactorialConvolutionTerm z w n k =
  Algebra._*C_
    (Factorial.originalBishopFactorialComplexTerm z k)
    (Factorial.originalBishopFactorialComplexTerm
      w (n ℕ.∸ k))

complexBinomialConvolutionTerm :
  Complex.BishopComplex → Complex.BishopComplex →
  Nat → Nat → Complex.BishopComplex
complexBinomialConvolutionTerm z w n k =
  Algebra.scaleC
    (BishopReal._*_
      (NatReal.natReal (n Comb.C k))
      (Exp.embed (Exp.inverseFactorial n)))
    (Algebra._*C_
      (Algebra.powC z k)
      (Algebra.powC w (n ℕ.∸ k)))

-- Both definitions use precisely the stdlib Fin(suc n) semiring sum
-- on the SAME Bishop-real coordinate carrier.
complexFactorialConvolutionCoefficient :
  Complex.BishopComplex → Complex.BishopComplex →
  Nat → Complex.BishopComplex
complexFactorialConvolutionCoefficient z w n =
  Complex.complex
    (BishopSum.sum {n = suc n}
      (λ index →
        Complex.re
          (complexFactorialConvolutionTerm z w n (toℕ index))))
    (BishopSum.sum {n = suc n}
      (λ index →
        Complex.im
          (complexFactorialConvolutionTerm z w n (toℕ index))))

complexBinomialConvolutionCoefficient :
  Complex.BishopComplex → Complex.BishopComplex →
  Nat → Complex.BishopComplex
complexBinomialConvolutionCoefficient z w n =
  Complex.complex
    (BishopSum.sum {n = suc n}
      (λ index →
        Complex.re
          (complexBinomialConvolutionTerm z w n (toℕ index))))
    (BishopSum.sum {n = suc n}
      (λ index →
        Complex.im
          (complexBinomialConvolutionTerm z w n (toℕ index))))

originalBishopComplexFiniteFactorialCoefficientIsBinomial :
  ∀ z w n →
  Complex._≈C_
    (complexFactorialConvolutionCoefficient z w n)
    (complexBinomialConvolutionCoefficient z w n)
originalBishopComplexFiniteFactorialCoefficientIsBinomial
  z w n =
  (BishopSum.sum-cong-≋
    (λ index →
      proj₁ (Summand.originalBishopComplexFactorialConvolutionSummand
        z w n (toℕ index)
        (FinP.toℕ≤pred[n] index))))
  ,
  (BishopSum.sum-cong-≋
    (λ index →
      proj₂ (Summand.originalBishopComplexFactorialConvolutionSummand
        z w n (toℕ index)
        (FinP.toℕ≤pred[n] index))))
