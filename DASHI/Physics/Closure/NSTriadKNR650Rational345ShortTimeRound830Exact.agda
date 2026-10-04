{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345ShortTimeRound830Exact where

------------------------------------------------------------------------
-- R830 / EXACT ARITHMETIC RECEIPT FOR THE R828 SHORT-TIME ENCLOSURE
--
-- The analytic finite-ODE proof in R828 supplies the rational horizon
--
--   T = 226189 / 3938540454339300631433585885184 > 0
--
-- and the uniform bound
--
--   rate(t) <= -226189/2  on  [0,T].
--
-- This owner kernel-checks the exact endpoint arithmetic needed by the final
-- integration step.  It does NOT claim the real finite-dimensional ODE
-- existence/continuity theorem or the R829 same-object component evaluation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _*_; _/_; -_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Decidable.Core using (toWitness)

shortTime345 : ℚ
shortTime345 =
  (+ 226189) / 3938540454339300631433585885184

rateUpper345 : ℚ
rateUpper345 = - ((+ 226189) / 2)

integratedUpper345 : ℚ
integratedUpper345 = rateUpper345 * shortTime345

shortTime345Positive : 0ℚ < shortTime345
shortTime345Positive =
  toWitness (ℚP._<?_ 0ℚ shortTime345)

rateUpper345Negative : rateUpper345 < 0ℚ
rateUpper345Negative =
  toWitness (ℚP._<?_ rateUpper345 0ℚ)

integratedUpper345Negative : integratedUpper345 < 0ℚ
integratedUpper345Negative =
  toWitness (ℚP._<?_ integratedUpper345 0ℚ)

------------------------------------------------------------------------
-- A deliberately minimal analytic interface.  A real-time finite ODE owner
-- should supply the rate bound and an order-preserving integral comparison;
-- after that, no additional Navier--Stokes-specific estimate is needed.
------------------------------------------------------------------------

record ShortTimeIntegralTransport : Set₁ where
  field
    Time : Set
    initial terminal : Time
    rate : Time → ℚ
    integrateTo : (Time → ℚ) → Time → ℚ

    onSelectedInterval : Time → Set

    initialIncluded : onSelectedInterval initial
    terminalIncluded : onSelectedInterval terminal

    pointwiseRateBound :
      (time : Time) → onSelectedInterval time →
      rate time < 0ℚ

    integratedStrictNegativity :
      ((time : Time) → onSelectedInterval time → rate time < 0ℚ) →
      integrateTo rate terminal < 0ℚ

open ShortTimeIntegralTransport public

transportedIntegralNegative :
  (certificate : ShortTimeIntegralTransport) →
  integrateTo certificate (rate certificate) (terminal certificate) < 0ℚ
transportedIntegralNegative certificate =
  integratedStrictNegativity certificate
    (pointwiseRateBound certificate)

------------------------------------------------------------------------
-- Status boundary.
------------------------------------------------------------------------

round830ExactHorizonArithmeticClosed : Bool
round830ExactHorizonArithmeticClosed = true

round830ExactNegativeIntegralUpperBoundClosed : Bool
round830ExactNegativeIntegralUpperBoundClosed = true

round830RealFiniteODEExistenceContinuityFormalized : Bool
round830RealFiniteODEExistenceContinuityFormalized = false

round830R829SameObjectIdentificationConsumed : Bool
round830R829SameObjectIdentificationConsumed = false

round830UniversalR823ReserveRefutedInKernel : Bool
round830UniversalR823ReserveRefutedInKernel = false

round830ClayPromotion : Bool
round830ClayPromotion = false

round830ExactHorizonArithmeticClosedIsTrue :
  round830ExactHorizonArithmeticClosed ≡ true
round830ExactHorizonArithmeticClosedIsTrue = refl

round830RealFiniteODEExistenceContinuityFormalizedIsFalse :
  round830RealFiniteODEExistenceContinuityFormalized ≡ false
round830RealFiniteODEExistenceContinuityFormalizedIsFalse = refl
