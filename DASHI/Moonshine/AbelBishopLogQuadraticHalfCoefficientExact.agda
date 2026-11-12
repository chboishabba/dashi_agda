module DASHI.Moonshine.AbelBishopLogQuadraticHalfCoefficientExact where

------------------------------------------------------------------------
-- LITERAL BISHOP LOG(1+u) QUADRATIC TAIL COEFFICIENT <= 1/2.
--
-- Original source: a_n(u)=(-1)^n u^(n+1)/(n+1).
-- For every n, shifted a_(n+1) has coefficient
-- magnitude 1/(n+2) <= 1/2, proved by exact Nat fraction order.
--
-- The existing full-series bound <=1 lost this factor of 1/2.
-- This file restores it and transports it to the original upper-disk
-- complex power envelope, with no derivative or alternative log.
--
-- Quantitative limit comparison to sum r^(n+2)/2, branch inversion
-- and the actual original inverse-Koenigs orbit remain separate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (z≤n; s≤s)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; 0ℚᵘ; _/_; _≤_)
import Data.Rational.Unnormalised.Properties as RationalP

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexNormSquareUpperPowerEnvelopeExact as Upper
import DASHI.Mathematics.NumberTheory.FiniteNatFractionOrderExact as NatFraction
import DASHI.Foundations.BishopNegativeExponentialInterlacingExact as Reciprocal
import DASHI.Moonshine.AbelBishopLogOnePlusOriginalSeriesExact as Log

halfRational : ℚᵘ
halfRational = + 1 / 2

bishopHalf : BishopReal.ℝ
bishopHalf = BishopReal._⋆ halfRational

bishopHalfNonnegative : BishopReal.NonNegative bishopHalf
bishopHalfNonnegative =
  BishopP.pos⇒nonNeg
    (BishopP.0<x⇒posx
      (BishopP.p<q⇒p⋆<q⋆
        0ℚᵘ halfRational
        (RationalP.positive⁻¹ halfRational)))

originalShiftedLogCoefficientRationalBelowHalf :
  ∀ n →
  ℚ._≤_ (Log.inversePositiveNat (suc n)) halfRational
originalShiftedLogCoefficientRationalBelowHalf n =
  NatFraction.natFractionLe
    (s≤s (s≤s z≤n))

originalShiftedBishopLogCoefficientBelowHalf :
  ∀ n →
  BishopReal._≤_
    (BishopReal.∣ Log.logCoefficient (suc n) ∣)
    bishopHalf
originalShiftedBishopLogCoefficientBelowHalf n
  with Log.alternate (suc n)
... | false =
  BishopP.≤-respˡ-≃
    (BishopP.nonNegx⇒∣x∣≃x
      (Reciprocal.reciprocalNonnegative (suc n)))
    (BishopP.p≤q⇒p⋆≤q⋆
      (Log.inversePositiveNat (suc n))
      halfRational
      (originalShiftedLogCoefficientRationalBelowHalf n))
... | true =
  BishopP.≤-respˡ-≃
    (BishopP.≃-trans
      BishopP.∣-x∣≃∣x∣
      (BishopP.nonNegx⇒∣x∣≃x
        (Reciprocal.reciprocalNonnegative (suc n))))
    (BishopP.p≤q⇒p⋆≤q⋆
      (Log.inversePositiveNat (suc n))
      halfRational
      (originalShiftedLogCoefficientRationalBelowHalf n))

originalBishopHalfCoefficientScalarProduct :
  ∀ scalar x →
  BishopReal._≤_ (BishopReal.∣ scalar ∣) bishopHalf →
  BishopReal._≤_
    (BishopReal.∣ BishopReal._*_ scalar x ∣)
    (BishopReal._*_ bishopHalf (BishopReal.∣ x ∣))
originalBishopHalfCoefficientScalarProduct scalar x coefficientBound =
  BishopP.≤-respˡ-≃
    (BishopP.∣x*y∣≃∣x∣*∣y∣ scalar x)
    (BishopP.*-monoʳ-≤-nonNeg
      coefficientBound
      (BishopP.nonNeg∣x∣ x))

originalBishopLogQuadraticRealTermUpper :
  ∀ {w radius} →
  (disk : Upper.BishopComplexNormSquareUpperRadius w radius) →
  ∀ n →
  BishopReal._≤_
    (BishopReal.∣ Complex.re
      (Log.originalBishopLogOnePlusTerm w (suc n)) ∣)
    (BishopReal._*_
      bishopHalf
      (BishopReal.pow radius (suc (suc n))))
originalBishopLogQuadraticRealTermUpper {w} disk n =
  BishopP.≤-trans
    (originalBishopHalfCoefficientScalarProduct
      (Log.logCoefficient (suc n))
      (Complex.re (Algebra.powC w (suc (suc n))))
      (originalShiftedBishopLogCoefficientBelowHalf n))
    (BishopP.*-monoˡ-≤-nonNeg
      (Upper.realPowerUpper disk (suc (suc n)))
      bishopHalfNonnegative)

originalBishopLogQuadraticImagTermUpper :
  ∀ {w radius} →
  (disk : Upper.BishopComplexNormSquareUpperRadius w radius) →
  ∀ n →
  BishopReal._≤_
    (BishopReal.∣ Complex.im
      (Log.originalBishopLogOnePlusTerm w (suc n)) ∣)
    (BishopReal._*_
      bishopHalf
      (BishopReal.pow radius (suc (suc n))))
originalBishopLogQuadraticImagTermUpper {w} disk n =
  BishopP.≤-trans
    (originalBishopHalfCoefficientScalarProduct
      (Log.logCoefficient (suc n))
      (Complex.im (Algebra.powC w (suc (suc n))))
      (originalShiftedBishopLogCoefficientBelowHalf n))
    (BishopP.*-monoˡ-≤-nonNeg
      (Upper.imagPowerUpper disk (suc (suc n)))
      bishopHalfNonnegative)
