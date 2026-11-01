{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2CompositeTailWeldValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayLevel2CompositeTailWeldExact as D1

noSecondCompositeTailDecayTheorem :
  D1.newCompositeTailDecayTheoremRequiredByD1 ≡ false
noSecondCompositeTailDecayTheorem = refl

noSecondContinuumCompositeCompletionTheorem :
  D1.newContinuumCompositeCompletionTheoremRequiredByD1 ≡ false
noSecondContinuumCompositeCompletionTheorem = refl

sameCompletedCompositeAttachmentRemainsPhysical :
  D1.sameCompletedCompositeTailAttachmentStillPhysical ≡ true
sameCompletedCompositeAttachmentRemainsPhysical = refl

promotionFailClosed :
  D1.clayPromotion ≡ false
promotionFailClosed = refl
