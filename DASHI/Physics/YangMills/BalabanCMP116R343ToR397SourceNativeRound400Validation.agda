{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R343ToR397SourceNativeRound400Validation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanCMP116R343ToR397SourceNativeRound400Exact as R400

compilerOwned : R400.r343ToCurrentOneSidedCompilerOwned ≡ true
compilerOwned = refl

actualSourceRatioPreserved : R400.r343RoutePreservesActualSourceRatio ≡ true
actualSourceRatioPreserved = refl

attachmentPaidForR343Producer :
  R400.r343RoutePaysCurrentAttachmentForItsOwnProducer ≡ true
attachmentPaidForR343Producer = refl

geometryPaidForR343Producer :
  R400.r343RoutePaysCurrentGeometryForItsOwnProducer ≡ true
geometryPaidForR343Producer = refl

noConcreteR343InhabitantConstructed :
  R400.r343ConcreteInhabitantConstructedHere ≡ false
noConcreteR343InhabitantConstructed = refl

r343NotMandatory : R400.r343RouteMandatoryArchitecture ≡ false
r343NotMandatory = refl

noClayPromotion : R400.clayPromotion ≡ false
noClayPromotion = refl
