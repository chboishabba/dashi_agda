module DASHI.Foundations.BishopExponentialBinomialCoefficientExact where

------------------------------------------------------------------------
-- BISHOP EXPONENTIAL FINITE BINOMIAL COEFFICIENT BRIDGE
--
-- This owner connects three existing exact layers:
--
--   * stdlib commutative-semiring binomial theorem;
--   * stdlib factorial/binomial arithmetic, via
--     FiniteBinomialInverseFactorialExact;
--   * the concrete Bishop exponential coefficient x^n/n!.
--
-- No convergence occurs here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Combinatorics using (_C_)
open import Data.Rational.Unnormalised using (1ℚᵘ)

import Algebra.Properties.CommutativeSemiring.Binomial as Binomial
import Algebra.Properties.Semiring.Exp as SemiringExp
import Algebra.Properties.Semiring.Mult as SemiringMult

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as NatReal
import DASHI.Mathematics.NumberTheory.FiniteBinomialInverseFactorialExact as Coeff
open import DASHI.Physics.YangMills.CompactLieProofLevel

module BishopBinomial =
  Binomial BishopP.+-*-commutativeSemiring

module BishopSemiringExp =
  SemiringExp BishopP.+-*-semiring

module BishopSemiringMult =
  SemiringMult BishopP.+-*-semiring

------------------------------------------------------------------------
-- The stdlib semiring power multiplies on the left; vendor/bishop's `pow`
-- multiplies on the right.  Commutativity identifies them.

stdlibPowerIsBishopPow :
  ∀ value exponent →
  BishopReal._≃_
    (BishopSemiringExp._^_ value exponent)
    (BishopReal.pow value exponent)
stdlibPowerIsBishopPow value zero = BishopP.≃-refl
stdlibPowerIsBishopPow value (suc exponent) =
  BishopP.≃-trans
    (BishopP.*-congˡ (stdlibPowerIsBishopPow value exponent))
    (BishopP.*-comm value (BishopReal.pow value exponent))

------------------------------------------------------------------------
-- Embedded naturals agree with stdlib repeated addition of one.

natRealIsNaturalScaleOne :
  ∀ n →
  BishopReal._≃_
    (NatReal.natReal n)
    (BishopSemiringMult._×_ n BishopReal.1ℝ)
natRealIsNaturalScaleOne zero = BishopP.≃-refl
natRealIsNaturalScaleOne (suc n) =
  BishopP.≃-trans
    (NatReal.natRealSuccessor n)
    (BishopP.+-cong
      (natRealIsNaturalScaleOne n)
      BishopP.≃-refl)

naturalScaleAsEmbeddedMultiply :
  ∀ n value →
  BishopReal._≃_
    (BishopSemiringMult._×_ n value)
    (BishopReal._*_ (NatReal.natReal n) value)
naturalScaleAsEmbeddedMultiply n value =
  BishopP.≃-symm
    (BishopP.≃-trans
      (BishopP.*-congʳ (natRealIsNaturalScaleOne n))
      (BishopP.≃-trans
        (BishopSemiringMult.×-assoc-* n BishopReal.1ℝ value)
        (BishopSemiringMult.×-congʳ n
          (BishopP.*-identityˡ value))))

------------------------------------------------------------------------
-- Reciprocal factorial coefficient identity after embedding.

embeddedInverseFactorialProductBinomial :
  ∀ {n k : Nat} →
  k Data.Nat.Base.≤ n →
  BishopReal._≃_
    (BishopReal._*_
      (Exp.embed (Exp.inverseFactorial k))
      (Exp.embed (Exp.inverseFactorial (n Data.Nat.Base.∸ k))))
    (BishopReal._*_
      (NatReal.natReal (n C k))
      (Exp.embed (Exp.inverseFactorial n)))
embeddedInverseFactorialProductBinomial {n} {k} k≤n =
  BishopP.≃-trans
    (BishopP.≃-symm
      (BishopP.⋆-distrib-*
        (Exp.inverseFactorial k)
        (Exp.inverseFactorial (n Data.Nat.Base.∸ k))))
    (BishopP.≃-trans
      (BishopP.⋆-cong
        (Coeff.inverseFactorialProductBinomial k≤n))
      (BishopP.⋆-distrib-*
        (+ (n C k) / 1)
        (Exp.inverseFactorial n)))

------------------------------------------------------------------------
-- One convolution summand becomes the corresponding binomial summand times
-- the common inverse n! factor.

expConvolutionTermBinomial :
  ∀ left right n k →
  k Data.Nat.Base.≤ n →
  BishopReal._≃_
    (BishopReal._*_
      (Exp.expTerm left k)
      (Exp.expTerm right (n Data.Nat.Base.∸ k)))
    (BishopReal._*_
      (BishopReal._*_
        (NatReal.natReal (n C k))
        (BishopReal._*_
          (BishopReal.pow left k)
          (BishopReal.pow right (n Data.Nat.Base.∸ k))))
      (Exp.embed (Exp.inverseFactorial n)))
expConvolutionTermBinomial left right n k k≤n =
  let
    leftPower = BishopReal.pow left k
    rightPower = BishopReal.pow right (n Data.Nat.Base.∸ k)
    leftCoeff = Exp.embed (Exp.inverseFactorial k)
    rightCoeff = Exp.embed (Exp.inverseFactorial (n Data.Nat.Base.∸ k))
    commonCoeff = Exp.embed (Exp.inverseFactorial n)
    chooseReal = NatReal.natReal (n C k)
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (solve 4
      (λ lp lc rp rc →
        (lp ⊗ lc) ⊗ (rp ⊗ rc)
        ⊜ (lp ⊗ rp) ⊗ (lc ⊗ rc))
      BishopP.≃-refl
      leftPower leftCoeff rightPower rightCoeff)
    (BishopP.≃-trans
      (BishopP.*-congˡ
        (embeddedInverseFactorialProductBinomial k≤n))
      (solve 4
        (λ lp rp choose common →
          (lp ⊗ rp) ⊗ (choose ⊗ common)
          ⊜ (choose ⊗ (lp ⊗ rp)) ⊗ common)
        BishopP.≃-refl
        leftPower rightPower chooseReal commonCoeff))

bishopExponentialFiniteBinomialCoefficientLevel : ProofLevel
bishopExponentialFiniteBinomialCoefficientLevel = machineChecked
