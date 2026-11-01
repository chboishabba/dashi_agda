module DASHI.Physics.YangMills.BalabanCMP116DirectHessianDistanceUpperRound381Validation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false; true)

import DASHI.Physics.YangMills.BalabanCMP116DirectHessianDistanceUpperRound381Exact as R381

r380EqualityNoLongerMandatory :
  R381.r380ExactDistanceEqualityMandatoryForCoefficient ≡ false
r380EqualityNoLongerMandatory =
  R381.r380ExactDistanceEqualityMandatoryForCoefficientIsFalse

pointwiseUpperRemainsProofBearing :
  R381.pointwiseHessianDistanceUpperStillProofBearing ≡ true
pointwiseUpperRemainsProofBearing =
  R381.pointwiseHessianDistanceUpperStillProofBearingIsTrue

noClayPromotion : R381.clayPromotion ≡ false
noClayPromotion = R381.clayPromotionIsFalse
