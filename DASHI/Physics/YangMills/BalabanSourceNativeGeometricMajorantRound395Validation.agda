{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSourceNativeGeometricMajorantRound395Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.BalabanSourceNativeGeometricMajorantRound395Exact as R395

halfUpperNotPrimitive :
  R395.fastRatioAtMostHalfRequired ≡ false
halfUpperNotPrimitive = R395.fastRatioAtMostHalfRequiredIsFalse

dyadicMayStillProduce :
  R395.dyadicMajorantStillOptionalProducer ≡ true
dyadicMayStillProduce = R395.dyadicMajorantStillOptionalProducerIsTrue

sourceNativeBoundRetained :
  R395.sourceNativeGeometricBoundIsPrimitiveInterface ≡ true
sourceNativeBoundRetained = R395.sourceNativeGeometricBoundIsPrimitiveInterfaceIsTrue

noClayPromotion : R395.clayPromotion ≡ false
noClayPromotion = R395.clayPromotionIsFalse
