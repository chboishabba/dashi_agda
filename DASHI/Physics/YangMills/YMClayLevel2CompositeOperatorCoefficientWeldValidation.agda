{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2CompositeOperatorCoefficientWeldValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayLevel2CompositeOperatorCoefficientWeldExact as D2

noSecondMixingMap :
  D2.secondMixingMapAbstractionRequiredByD2 ≡ false
noSecondMixingMap = refl

noSecondGlobalAFTheorem :
  D2.globalAFTheoremRequiredByD2 ≡ false
noSecondGlobalAFTheorem = refl

noSecondAllDepthComparison :
  D2.allDepthComparisonRequiredByD2 ≡ false
noSecondAllDepthComparison = refl

sameOperatorTrajectoryAttachmentStillPhysical :
  D2.sameCompositeOperatorTrajectoryAttachmentStillPhysical ≡ true
sameOperatorTrajectoryAttachmentStillPhysical = refl

promotionFailClosed :
  D2.clayPromotion ≡ false
promotionFailClosed = refl
