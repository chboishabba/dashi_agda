module DASHI.Foundations.BishopExponentialFiniteCauchyCoefficientExact where

------------------------------------------------------------------------
-- FINITE CAUCHY COEFFICIENT FOR THE BISHOP EXPONENTIAL
--
-- For every n,
--
--   sum_{k=0}^n expTerm(x,k) expTerm(y,n-k)
--     ~= expTerm(x+y,n).
--
-- The sum is the stdlib Fin(suc n) semiring sum, so the proof can reuse the
-- stdlib setoid binomial theorem literally.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin.Base using (Fin; toℕ)
import Data.Fin.Properties as FinP
import Data.Nat.Base as ℕ
import Data.Nat.Combinatorics as Comb

import Algebra.Properties.Semiring.Sum as SemiringSum

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialBinomialCoefficientExact as Coeff
import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as NatReal
open import DASHI.Physics.YangMills.CompactLieProofLevel

module BishopSum = SemiringSum BishopP.+-*-semiring

cauchyCoefficient :
  BishopReal.ℝ → BishopReal.ℝ → Nat → BishopReal.ℝ
cauchyCoefficient left right n =
  BishopSum.sum
    (λ index →
      BishopReal._*_
        (Exp.expTerm left (toℕ index))
        (Exp.expTerm right (n ℕ.∸ toℕ index)))

private
  convolutionTerm :
    BishopReal.ℝ → BishopReal.ℝ →
    (n : Nat) → Fin (suc n) → BishopReal.ℝ
  convolutionTerm left right n index =
    BishopReal._*_
      (Exp.expTerm left (toℕ index))
      (Exp.expTerm right (n ℕ.∸ toℕ index))

  scaledBinomialTerm :
    BishopReal.ℝ → BishopReal.ℝ →
    (n : Nat) → Fin (suc n) → BishopReal.ℝ
  scaledBinomialTerm left right n index =
    BishopReal._*_
      (Coeff.BishopBinomial.binomialTerm left right n index)
      (Exp.embed (Exp.inverseFactorial n))

convolutionTermIsScaledBinomial :
  ∀ left right n (index : Fin (suc n)) →
  BishopReal._≃_
    (convolutionTerm left right n index)
    (scaledBinomialTerm left right n index)
convolutionTermIsScaledBinomial left right n index =
  let
    k = toℕ index
    k≤n = FinP.toℕ≤pred[n] index
    leftPower = BishopReal.pow left k
    rightPower = BishopReal.pow right (n ℕ.∸ k)
    stdLeftPower = Coeff.BishopSemiringExp._^_ left k
    stdRightPower = Coeff.BishopSemiringExp._^_ right (n ℕ.∸ k)
    choose = n Comb.C k
    common = Exp.embed (Exp.inverseFactorial n)

    powers :
      BishopReal._≃_
        (BishopReal._*_ leftPower rightPower)
        (BishopReal._*_ stdLeftPower stdRightPower)
    powers =
      BishopP.*-cong
        (BishopP.≃-symm (Coeff.stdlibPowerIsBishopPow left k))
        (BishopP.≃-symm
          (Coeff.stdlibPowerIsBishopPow right (n ℕ.∸ k)))

    chooseTerm :
      BishopReal._≃_
        (BishopReal._*_
          (NatReal.natReal choose)
          (BishopReal._*_ leftPower rightPower))
        (Coeff.BishopBinomial.binomialTerm left right n index)
    chooseTerm =
      BishopP.≃-trans
        (BishopP.*-congˡ powers)
        (BishopP.≃-symm
          (Coeff.naturalScaleAsEmbeddedMultiply
            choose
            (BishopReal._*_ stdLeftPower stdRightPower)))
  in
  BishopP.≃-trans
    (Coeff.expConvolutionTermBinomial left right n k k≤n)
    (BishopP.*-congʳ chooseTerm)

finiteConvolutionIsScaledBinomialExpansion :
  ∀ left right n →
  BishopReal._≃_
    (cauchyCoefficient left right n)
    (BishopReal._*_
      (Coeff.BishopBinomial.binomialExpansion left right n)
      (Exp.embed (Exp.inverseFactorial n)))
finiteConvolutionIsScaledBinomialExpansion left right n =
  BishopP.≃-trans
    (BishopSum.sum-cong-≋
      (convolutionTermIsScaledBinomial left right n))
    (BishopP.≃-symm
      (BishopSum.*-distribʳ-sum
        (Exp.embed (Exp.inverseFactorial n))
        (Coeff.BishopBinomial.binomialTerm left right n)))

scaledBinomialExpansionIsExpTermSum :
  ∀ left right n →
  BishopReal._≃_
    (BishopReal._*_
      (Coeff.BishopBinomial.binomialExpansion left right n)
      (Exp.embed (Exp.inverseFactorial n)))
    (Exp.expTerm (BishopReal._+_ left right) n)
scaledBinomialExpansionIsExpTermSum left right n =
  BishopP.≃-trans
    (BishopP.*-congʳ
      (BishopP.≃-symm
        (Coeff.BishopBinomial.theorem n left right)))
    (BishopP.*-congʳ
      (Coeff.stdlibPowerIsBishopPow
        (BishopReal._+_ left right) n))

finiteExponentialCauchyCoefficient :
  ∀ left right n →
  BishopReal._≃_
    (cauchyCoefficient left right n)
    (Exp.expTerm (BishopReal._+_ left right) n)
finiteExponentialCauchyCoefficient left right n =
  BishopP.≃-trans
    (finiteConvolutionIsScaledBinomialExpansion left right n)
    (scaledBinomialExpansionIsExpTermSum left right n)

bishopExponentialFiniteCauchyCoefficientLevel : ProofLevel
bishopExponentialFiniteCauchyCoefficientLevel = machineChecked
