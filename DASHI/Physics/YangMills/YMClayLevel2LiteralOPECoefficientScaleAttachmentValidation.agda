{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2LiteralOPECoefficientScaleAttachmentValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayLevel2LiteralOPECoefficientScaleAttachmentExact as D2c

literalCoefficientNotNatIndexed :
  D2c.literalClayOPECoefficientIsNatIndexed ≡ false
literalCoefficientNotNatIndexed = refl

positionDepthSemanticsRemainPhysical :
  D2c.positionDepthSemanticsRequired ≡ true
positionDepthSemanticsRemainPhysical = refl

noSecondAllDepthComparison :
  D2c.secondAllDepthCoefficientComparisonRequired ≡ false
noSecondAllDepthComparison = refl

promotionFailClosed :
  D2c.clayPromotion ≡ false
promotionFailClosed = refl
