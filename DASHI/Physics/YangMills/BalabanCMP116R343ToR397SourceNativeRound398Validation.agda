{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R343ToR397SourceNativeRound398Validation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanCMP116R343ToR397SourceNativeRound398Exact as R398

compilerOwned : R398.r343ToCurrentOneSidedCompilerOwned ≡ true
compilerOwned = refl

actualSourceRatioPreserved : R398.r343RoutePreservesActualSourceRatio ≡ true
actualSourceRatioPreserved = refl

attachmentPaidForR343Producer :
  R398.r343RoutePaysCurrentAttachmentForItsOwnProducer ≡ true
attachmentPaidForR343Producer = refl

geometryPaidForR343Producer :
  R398.r343RoutePaysCurrentGeometryForItsOwnProducer ≡ true
geometryPaidForR343Producer = refl

noConcreteR343InhabitantConstructed :
  R398.r343ConcreteInhabitantConstructedHere ≡ false
noConcreteR343InhabitantConstructed = refl

r343NotMandatory : R398.r343RouteMandatoryArchitecture ≡ false
r343NotMandatory = refl

noClayPromotion : R398.clayPromotion ≡ false
noClayPromotion = refl
