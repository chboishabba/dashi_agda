{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2R129CompositeTailAttachmentValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YMClayLevel2R129CompositeTailAttachmentExact as D1

noIndependentCompositeMarkedSourceAfterR129 :
  D1.independentCompositeMarkedSourceAfterR129 ≡ false
noIndependentCompositeMarkedSourceAfterR129 = refl

noIndependentCompositeCompletionAfterR129 :
  D1.independentCompositeCompletionAfterR129 ≡ false
noIndependentCompositeCompletionAfterR129 = refl

d1ResidueIsOneTailEquality :
  D1.d1PhysicalResidueIsSingleTailEquality ≡ true
d1ResidueIsOneTailEquality = refl

promotionFailClosed :
  D1.clayPromotion ≡ false
promotionFailClosed = refl
