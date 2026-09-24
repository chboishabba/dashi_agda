{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.DrellYanRatioAbsoluteDefectLocalizationValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Closure.DrellYanRatioAbsoluteDefectLocalizationExact as D

sharedCarrierNotGloballyRejected :
  D.sameUnderlyingCarrierGloballyRejected
    D.canonicalDrellYanRatioAbsoluteDefectLocalization
  ≡ false
sharedCarrierNotGloballyRejected = refl

projectionSearchPreferred :
  D.nextDefectSearchTargetsProjectionSpecificStructure
    D.canonicalDrellYanRatioAbsoluteDefectLocalization
  ≡ true
projectionSearchPreferred = refl
