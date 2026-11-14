{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345OptimalEnvelopeRound856Exact where

------------------------------------------------------------------------
-- R856: EXACT BEST INTEGER R855 MULTIPLIERS ON ORIGINAL R829/R854 r0,L,T.
-- The *scalar affine* pointwise/integrated negativity is exact below
-- -r0/(L*T) and -2*r0/(L*T), respectively (L,T > 0).
-- Neighboring integer witnesses, not a physical Galerkin rate estimate.
-- Source: original DASHI R829/R854/R855; finite rational arithmetic.
-- No new postulates; pinned Agda 2.9 kernel check still required.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _/_; _+_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Decidable.Core using (toWitness)
import DASHI.Physics.Closure.NSTriadKNR650Rational345LipschitzIntegralRound854Exact as R854

pointwiseLargestSafeInteger856 : ℚ
pointwiseLargestSafeInteger856 = (+ 10065030) / 1

pointwiseFirstUnsafeInteger856 : ℚ
pointwiseFirstUnsafeInteger856 = (+ 10065031) / 1

integratedLargestSafeInteger856 : ℚ
integratedLargestSafeInteger856 = (+ 20130061) / 1

integratedFirstUnsafeInteger856 : ℚ
integratedFirstUnsafeInteger856 = (+ 20130062) / 1

pointwiseFloorTerminal856 : ℚ
pointwiseFloorTerminal856 =
  R854.actualInitialSelectedRate854
  + (pointwiseLargestSafeInteger856 * R854.sourceLipschitzConstant854)
    * R854.exactHorizon854

pointwiseCeilTerminal856 : ℚ
pointwiseCeilTerminal856 =
  R854.actualInitialSelectedRate854
  + (pointwiseFirstUnsafeInteger856 * R854.sourceLipschitzConstant854)
    * R854.exactHorizon854

integratedFloorAffine856 : ℚ
integratedFloorAffine856 =
  R854.actualInitialSelectedRate854 * R854.exactHorizon854
  + ((integratedLargestSafeInteger856 * R854.sourceLipschitzConstant854)
     * R854.exactHorizon854 * R854.exactHorizon854) / 2

integratedCeilAffine856 : ℚ
integratedCeilAffine856 =
  R854.actualInitialSelectedRate854 * R854.exactHorizon854
  + ((integratedFirstUnsafeInteger856 * R854.sourceLipschitzConstant854)
     * R854.exactHorizon854 * R854.exactHorizon854) / 2

pointwiseOptimalIntegerSafe856 :
  pointwiseFloorTerminal856 < 0ℚ
pointwiseOptimalIntegerSafe856 =
  toWitness (ℚP._<?_ pointwiseFloorTerminal856 0ℚ)

pointwiseNextIntegerNotSafe856 :
  0ℚ < pointwiseCeilTerminal856
pointwiseNextIntegerNotSafe856 =
  toWitness (ℚP._<?_ 0ℚ pointwiseCeilTerminal856)

integratedOptimalIntegerSafe856 :
  integratedFloorAffine856 < 0ℚ
integratedOptimalIntegerSafe856 =
  toWitness (ℚP._<?_ integratedFloorAffine856 0ℚ)

integratedNextIntegerNotSafe856 :
  0ℚ < integratedCeilAffine856
integratedNextIntegerNotSafe856 =
  toWitness (ℚP._<?_ 0ℚ integratedCeilAffine856)

physicalR853RateAlongActualCurveClosed856 : Bool
physicalR853RateAlongActualCurveClosed856 = false

physicalR853RateAlongActualCurveClosed856IsFalse :
  physicalR853RateAlongActualCurveClosed856 ≡ false
physicalR853RateAlongActualCurveClosed856IsFalse = refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
