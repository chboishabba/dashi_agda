{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2R129CompositeOperatorAttachmentValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayLevel2R129CompositeOperatorAttachmentExact as D2

arbitraryTransportDoesNotSuffice :
  D2.arbitraryCompositeOperatorTransportSufficesForLevel2D2 ≡ false
arbitraryTransportDoesNotSuffice = refl

sameFamilyAttachmentStillPhysical :
  D2.r129CompositeOperatorSameFamilyAttachmentStillPhysical ≡ true
sameFamilyAttachmentStillPhysical = refl

promotionFailClosed :
  D2.clayPromotion ≡ false
promotionFailClosed = refl
