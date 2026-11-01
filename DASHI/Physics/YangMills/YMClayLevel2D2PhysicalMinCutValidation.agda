{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2D2PhysicalMinCutValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayLevel2D2PhysicalMinCutExact as D2

noSecondMixingMap :
  D2.secondMixingMapResearchProblem ≡ false
noSecondMixingMap = refl

literalCoefficientNotConstantNatFamily :
  D2.literalClayCoefficientCanBeTreatedAsConstantNatFamily ≡ false
literalCoefficientNotConstantNatFamily = refl

positionDepthAttachmentStillPhysical :
  D2.positionDepthSemanticsIsIndependentPhysicalAttachment ≡ true
positionDepthAttachmentStillPhysical = refl


noParallelCompositeOperatorTheory :
  D2.parallelCompositeOperatorTheoryAllowed ≡ false
noParallelCompositeOperatorTheory = refl

r129SameFamilyOperatorAttachmentStillPhysical :
  D2.r129SameFamilyOperatorAttachmentStillPhysical ≡ true
r129SameFamilyOperatorAttachmentStillPhysical = refl

noSecondGlobalAFTheorem :
  D2.newGlobalAFTheoremRequired ≡ false
noSecondGlobalAFTheorem = refl

noSecondAllDepthCoefficientProof :
  D2.newAllDepthCoefficientProofRequired ≡ false
noSecondAllDepthCoefficientProof = refl

promotionFailClosed :
  D2.clayPromotion ≡ false
promotionFailClosed = refl
