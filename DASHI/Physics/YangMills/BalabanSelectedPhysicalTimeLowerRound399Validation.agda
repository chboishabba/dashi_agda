{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSelectedPhysicalTimeLowerRound399Validation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanSelectedPhysicalTimeLowerRound399Exact as R399

round399NoExactDistanceTime : R399.exactDistanceEqualsTimeRequired ≡ false
round399NoExactDistanceTime = refl

round399NoIndependentCarrier :
  R399.independentDistanceCarrierWeldRequired ≡ false
round399NoIndependentCarrier = refl

round399OneSidedGeometryRetained :
  R399.oneSidedSelectedSupportTimeGeometryStillProofBearing ≡ true
round399OneSidedGeometryRetained = refl

round399NoClayPromotion : R399.clayPromotion ≡ false
round399NoClayPromotion = refl
