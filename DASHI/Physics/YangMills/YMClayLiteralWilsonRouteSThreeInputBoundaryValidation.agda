{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralWilsonRouteSThreeInputBoundaryValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.YMClayLiteralWilsonRouteSThreeInputBoundaryExact as RouteS

exactThreeInputs :
  RouteS.exactlyThreePhysicalInputClasses ≡ true
exactThreeInputs = RouteS.exactlyThreePhysicalInputClassesIsTrue

s2NotIndependent :
  RouteS.literalEuclideanTimeSemanticsIndependentPhysicalLeaf ≡ false
s2NotIndependent =
  RouteS.literalEuclideanTimeSemanticsIndependentPhysicalLeafIsFalse

s3NotIndependent :
  RouteS.literalWilsonPresentationIndependentPhysicalLeaf ≡ false
s3NotIndependent =
  RouteS.literalWilsonPresentationIndependentPhysicalLeafIsFalse

markedSourceNotIndependent :
  RouteS.markedSourceCovarianceIdentityIndependentPhysicalLeaf ≡ false
markedSourceNotIndependent =
  RouteS.markedSourceCovarianceIdentityIndependentPhysicalLeafIsFalse

s4AlgebraNotIndependent :
  RouteS.covarianceLimitAlgebraIndependentPhysicalLeaf ≡ false
s4AlgebraNotIndependent =
  RouteS.covarianceLimitAlgebraIndependentPhysicalLeafIsFalse

terminalAssemblyNotIndependent :
  RouteS.terminalSpectralAssemblyIndependentPhysicalLeaf ≡ false
terminalAssemblyNotIndependent =
  RouteS.terminalSpectralAssemblyIndependentPhysicalLeafIsFalse

finiteClusteringRemainsPhysical :
  RouteS.finiteLiteralWilsonClusteringStillPhysical ≡ true
finiteClusteringRemainsPhysical =
  RouteS.finiteLiteralWilsonClusteringStillPhysicalIsTrue

expectationLimitsRemainPhysical :
  RouteS.threeLiteralWilsonExpectationLimitsStillPhysical ≡ true
expectationLimitsRemainPhysical =
  RouteS.threeLiteralWilsonExpectationLimitsStillPhysicalIsTrue

sameOSCorrelationRemainsPhysical :
  RouteS.sameOSCorrelationIdentificationStillPhysical ≡ true
sameOSCorrelationRemainsPhysical =
  RouteS.sameOSCorrelationIdentificationStillPhysicalIsTrue

leanTerminalCompilerVerified :
  RouteS.leanTerminalCompilerKernelRevalidated ≡ true
leanTerminalCompilerVerified =
  RouteS.leanTerminalCompilerKernelRevalidatedIsTrue

agdaDoesNotPretendToReproveLean :
  RouteS.agdaParityForTerminalLeanTheoremConstructedHere ≡ false
agdaDoesNotPretendToReproveLean =
  RouteS.agdaParityForTerminalLeanTheoremConstructedHereIsFalse

physicalInputsNotAutoInhabited :
  RouteS.threePhysicalInputsAreAutomaticallyInhabited ≡ false
physicalInputsNotAutoInhabited =
  RouteS.threePhysicalInputsAreAutomaticallyInhabitedIsFalse

noClayPromotion :
  RouteS.clayPromotion ≡ false
noClayPromotion = RouteS.clayPromotionIsFalse
