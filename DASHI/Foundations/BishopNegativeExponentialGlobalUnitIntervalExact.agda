module DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact where

------------------------------------------------------------------------
-- GLOBAL NEGATIVE-EXPONENTIAL UNIT-INTERVAL LAW
--
-- DASHI CONTRIBUTION
--
-- For every positive Bishop real x,
--
--     0 < exp(-x) < 1.
--
-- The older direct alternating-series owner constructed this only on
-- 0 < x <= 1.  Here the global statement is derived from:
--
--   * the concrete all-real exponential Cauchy-product law;
--   * the existing positive-side theorem 1 < exp(x);
--   * Bishop's checked constructive inverse and inverse-order laws.
--
-- No classical trichotomy or external real exponential is introduced.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as RatP
open import Data.Sum.Base using (inj₂)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialPositiveOrderExact as Positive
import DASHI.Foundations.BishopExponentialCauchyProductExact as Product

onePositive : BishopReal._<_ BishopReal.0ℝ BishopReal.1ℝ
onePositive =
  BishopP.p<q⇒p⋆<q⋆
    0ℚᵘ 1ℚᵘ (RatP.positive⁻¹ 1ℚᵘ)

oneNonzero : BishopReal._≄0 BishopReal.1ℝ
oneNonzero = inj₂ onePositive

inverseOneIsOne :
  BishopReal._≃_
    (BishopReal._⁻¹ BishopReal.1ℝ oneNonzero)
    BishopReal.1ℝ
inverseOneIsOne =
  BishopP.≃-symm
    (BishopInverse.⁻¹-unique
      BishopReal.1ℝ
      BishopReal.1ℝ
      oneNonzero
      (BishopP.*-identityʳ BishopReal.1ℝ))

expPositive :
  ∀ {x} →
  BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._<_ BishopReal.0ℝ (Exp.bishopExp x)
expPositive xPositive =
  BishopP.<-trans
    onePositive
    (Positive.bishopExpStrictlyAboveOneOnPositive xPositive)

expNonzero :
  ∀ {x} →
  (xPositive : BishopReal._<_ BishopReal.0ℝ x) →
  BishopReal._≄0 (Exp.bishopExp x)
expNonzero xPositive = inj₂ (expPositive xPositive)

negativeExpIsInversePositiveExp :
  ∀ {x} →
  (xPositive : BishopReal._<_ BishopReal.0ℝ x) →
  BishopReal._≃_
    (Exp.bishopExp (BishopReal.- x))
    (BishopReal._⁻¹
      (Exp.bishopExp x)
      (expNonzero xPositive))
negativeExpIsInversePositiveExp {x} xPositive =
  BishopInverse.⁻¹-unique
    (Exp.bishopExp (BishopReal.- x))
    (Exp.bishopExp x)
    (expNonzero xPositive)
    (BishopP.≃-trans
      (BishopP.*-comm
        (Exp.bishopExp (BishopReal.- x))
        (Exp.bishopExp x))
      (Product.bishopExpTimesNegativeIsOne x))

negativeExpPositive :
  ∀ {x} →
  BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._<_
    BishopReal.0ℝ
    (Exp.bishopExp (BishopReal.- x))
negativeExpPositive {x} xPositive =
  BishopP.<-respʳ-≃
    (BishopP.≃-symm
      (negativeExpIsInversePositiveExp xPositive))
    (BishopInverse.0<x⇒0<x⁻¹
      (expNonzero xPositive)
      (expPositive xPositive))

negativeExpBelowOne :
  ∀ {x} →
  BishopReal._<_ BishopReal.0ℝ x →
  BishopReal._<_
    (Exp.bishopExp (BishopReal.- x))
    BishopReal.1ℝ
negativeExpBelowOne {x} xPositive =
  let
    expX = Exp.bishopExp x
    expXNonzero = expNonzero xPositive
    expXPositive = BishopP.0<x⇒posx (expPositive xPositive)
    onePositiveWitness = BishopP.0<x⇒posx onePositive

    inverseOrder :
      BishopReal._<_
        (BishopReal._⁻¹ expX expXNonzero)
        (BishopReal._⁻¹ BishopReal.1ℝ oneNonzero)
    inverseOrder =
      BishopInverse.x<y∧posx,y⇒y⁻¹<x⁻¹
        (Positive.bishopExpStrictlyAboveOneOnPositive xPositive)
        oneNonzero
        expXNonzero
        onePositiveWitness
        expXPositive
  in
  BishopP.<-respʳ-≃
    inverseOneIsOne
    (BishopP.<-respˡ-≃
      (negativeExpIsInversePositiveExp xPositive)
      inverseOrder)
