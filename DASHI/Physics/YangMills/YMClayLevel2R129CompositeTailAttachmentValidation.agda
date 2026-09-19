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

d1ResidueIsCompletedCompositeSemanticWeld :
  D1.d1PhysicalResidueIsCompletedCompositeSemanticWeld ≡ true
d1ResidueIsCompletedCompositeSemanticWeld = refl

noNewD1AnalyticInequality :
  D1.d1NewAnalyticInequalityRequired ≡ false
noNewD1AnalyticInequality = refl

promotionFailClosed :
  D1.clayPromotion ≡ false
promotionFailClosed = refl
