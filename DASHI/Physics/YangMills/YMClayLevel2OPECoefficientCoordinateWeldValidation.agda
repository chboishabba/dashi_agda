{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2OPECoefficientCoordinateWeldValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayLevel2OPECoefficientCoordinateWeldExact as D2

noSecondGlobalAFTheorem :
  D2.newGlobalAFTheoremRequiredByD2 ≡ false
noSecondGlobalAFTheorem = refl

noSecondAllDepthCoefficientTheorem :
  D2.newAllDepthCoefficientTheoremRequiredByD2 ≡ false
noSecondAllDepthCoefficientTheorem = refl

sameCoordinateAttachmentRemainsPhysical :
  D2.sameCoordinateAttachmentStillPhysical ≡ true
sameCoordinateAttachmentRemainsPhysical = refl

promotionFailClosed :
  D2.clayPromotion ≡ false
promotionFailClosed = refl
