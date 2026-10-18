{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2SameFamilyStressRecoveryValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayLevel2SameFamilyStressRecoveryExact as L2

r127NotIndependentAfterR129 :
  L2.r127IndependentAfterR129Recovery ≡ false
r127NotIndependentAfterR129 = refl

continuumLimitNotIndependentAfterR129 :
  L2.literalContinuumLimitIndependentAfterR129Recovery ≡ false
continuumLimitNotIndependentAfterR129 = refl

schwingerMembershipNotIndependentAfterR129 :
  L2.literalSchwingerMembershipIndependentAfterR129Recovery ≡ false
schwingerMembershipNotIndependentAfterR129 = refl

stressDerivativeNotIndependentAfterR129 :
  L2.literalStressDerivativeIndependentAfterR129Recovery ≡ false
stressDerivativeNotIndependentAfterR129 = refl

promotionFailClosed :
  L2.clayPromotion ≡ false
promotionFailClosed = refl

compositeMarkedSourceNotIndependentAfterR129 :
  L2.compositeMarkedSourceDataIndependentAfterR129Recovery ≡ false
compositeMarkedSourceNotIndependentAfterR129 = refl
