{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116BoundaryScalarizationFactorRound386Validation where

import DASHI.Physics.YangMills.BalabanCMP116BoundaryScalarizationFactorRound386Exact as R386

open import Agda.Builtin.Equality using (_≡_; refl)

validationNoClayPromotion : R386.clayPromotion ≡ false
validationNoClayPromotion = refl

validationWholeScalarizationNoLongerPrimitive :
  R386.wholeBoundaryNormScalarizationPrimitiveAfterRound386 ≡ false
validationWholeScalarizationNoLongerPrimitive = refl

validationLiteralActivityAttachmentStillLive :
  R386.literalDecoupledSecondVariationAttachmentStillRequired ≡ true
validationLiteralActivityAttachmentStillLive = refl
