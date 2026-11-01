{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R343ToR397SourceNativeRound401Validation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanCMP116R343ToR397SourceNativeRound401Exact as R401

compilerOwned : R401.r343ToCurrentOneSidedCompilerOwned ≡ true
compilerOwned = refl

actualSourceRatioPreserved : R401.r343RoutePreservesActualSourceRatio ≡ true
actualSourceRatioPreserved = refl

attachmentPaidForR343Producer :
  R401.r343RoutePaysCurrentAttachmentForItsOwnProducer ≡ true
attachmentPaidForR343Producer = refl

geometryPaidForR343Producer :
  R401.r343RoutePaysCurrentGeometryForItsOwnProducer ≡ true
geometryPaidForR343Producer = refl

noConcreteR343InhabitantConstructed :
  R401.r343ConcreteInhabitantConstructedHere ≡ false
noConcreteR343InhabitantConstructed = refl

r343NotMandatory : R401.r343RouteMandatoryArchitecture ≡ false
r343NotMandatory = refl

noClayPromotion : R401.clayPromotion ≡ false
noClayPromotion = refl
