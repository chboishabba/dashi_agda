{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2D1PhysicalMinCutValidation where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.YMClayLevel2D1PhysicalMinCutExact as D1

noAuxiliaryProductRemainderFunction :
  D1.auxiliaryProductRemainderFunctionRequiredByD1 ≡ false
noAuxiliaryProductRemainderFunction =
  D1.auxiliaryProductRemainderFunctionRequiredByD1IsFalse

noIndependentCompositeCarrierAfterR129 :
  D1.independentCompositeCarrierRequiredAfterR129 ≡ false
noIndependentCompositeCarrierAfterR129 =
  D1.independentCompositeCarrierRequiredAfterR129IsFalse

noNewD1AnalyticInequality :
  D1.newD1AnalyticInequalityRequired ≡ false
noNewD1AnalyticInequality =
  D1.newD1AnalyticInequalityRequiredIsFalse

directRemainderEqualityRemainsPhysical :
  D1.directSameObjectRemainderEqualityStillPhysical ≡ true
directRemainderEqualityRemainsPhysical =
  D1.directSameObjectRemainderEqualityStillPhysicalIsTrue

promotionFailClosed :
  D1.clayPromotion ≡ false
promotionFailClosed = D1.clayPromotionIsFalse
