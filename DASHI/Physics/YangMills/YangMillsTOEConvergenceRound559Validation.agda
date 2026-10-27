{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsTOEConvergenceRound559Exact as TOE
open import DASHI.Physics.YangMills.CompactLieProofLevel

irreducibleFamilyCountIsFourteen :
  TOE.toeIrreducibleSourceFamilyCount ≡ 14
irreducibleFamilyCountIsFourteen = refl

criticalFamilyCountIsSeven :
  TOE.toeCriticalFamilyCount ≡ 7
criticalFamilyCountIsSeven = refl

concreteSemanticResidualIsThirtyThree :
  TOE.toeConcreteSemanticResidualCount ≡ 33
concreteSemanticResidualIsThirtyThree = refl

endpointSemanticResidualIsZero :
  TOE.toeEndpointSemanticResidualCount ≡ 0
endpointSemanticResidualIsZero = refl

opaqueEndpointsAreGone :
  TOE.toeOpaqueEndpointPredicatesRemaining ≡ false
opaqueEndpointsAreGone =
  TOE.toeOpaqueEndpointPredicatesRemainingIsFalse

constructorChoiceEqualitiesAreGone :
  TOE.toeConstructorChoiceEqualitiesRemaining ≡ false
constructorChoiceEqualitiesAreGone =
  TOE.toeConstructorChoiceEqualitiesRemainingIsFalse

remainingFamiliesAreNotAllProved :
  TOE.toeAllRemainingFamiliesAlreadyProved ≡ false
remainingFamiliesAreNotAllProved =
  TOE.toeAllRemainingFamiliesAlreadyProvedIsFalse

publishedRGDoesNotPromoteContinuum :
  TOE.toeFlat4DContinuumTransferProvedHere ≡ false
publishedRGDoesNotPromoteContinuum =
  TOE.toePublishedRGDoesNotPromoteContinuum

continuumMassGapRemainsNonPromoted :
  TOE.toeContinuumMassGapPromoted ≡ false
continuumMassGapRemainsNonPromoted =
  TOE.toeContinuumMassGapPromotedIsFalse

regularESourceClosureRemainsOpen :
  TOE.toeRegularEPhysicalSourceClosure ≡ false
regularESourceClosureRemainsOpen =
  TOE.toeRegularEPhysicalSourceClosureIsFalse

sourceNativeRegularEProjectionCompilerIsChecked :
  TOE.toePublishedFlowToRegularEProjectionCompilerLevel ≡ machineChecked
sourceNativeRegularEProjectionCompilerIsChecked = refl

regularESection2PredicateCompilerIsChecked :
  TOE.toeRegularESection2PredicateCompilerLevel ≡ machineChecked
regularESection2PredicateCompilerIsChecked = refl

regularELocalizationSourceIsImported :
  TOE.toeCMP119RegularELocalizationSourceLevel ≡ standardImported
regularELocalizationSourceIsImported = refl

regularELocalizationCarrierRemainsConditional :
  TOE.toeLiteralCMP119RegularELocalizationCarrierLevel ≡ conditional
regularELocalizationCarrierRemainsConditional = refl

concreteELocalizationSourceWitnessRemainsConditional :
  TOE.toeConcreteELocalizationSourceWitnessLevel ≡ conditional
concreteELocalizationSourceWitnessRemainsConditional = refl

stressRouteDoesNotPromoteClay :
  TOE.toeStressRouteClayPromotion ≡ false
stressRouteDoesNotPromoteClay =
  TOE.toeStressRouteClayPromotionIsFalse

currentHardAnalyticCutsetIsSix :
  TOE.toeHardAnalyticLemmaUpperCount ≡ 6
currentHardAnalyticCutsetIsSix =
  TOE.toeHardAnalyticLemmaUpperCountIsSix

casimirFloorCompilerIsChecked :
  TOE.toeCompactSimpleUniversalCasimirFloorLevel ≡ machineChecked
casimirFloorCompilerIsChecked = refl

stressChargeCutoffRemovalCompilerIsChecked :
  TOE.toeStressChargeLocalCoreCutoffRemovalLevel ≡ machineChecked
stressChargeCutoffRemovalCompilerIsChecked = refl

literalWilsonFPHaarLeafRemainsConditional :
  TOE.toeLiteralWilsonFPHaarFourJointOrbitHalfEnclosuresLevel ≡ conditional
literalWilsonFPHaarLeafRemainsConditional = refl

physicalStressWardLeafRemainsConditional :
  TOE.toePhysicalStressWardCommonCoreAndEssentialSelfAdjointnessLevel ≡ conditional
physicalStressWardLeafRemainsConditional = refl

clayYangMillsNotPromoted :
  TOE.toeClayYangMillsPromoted ≡ false
clayYangMillsNotPromoted =
  TOE.toeClayYangMillsPromotedIsFalse

toeConvergenceCompilerMachineChecked :
  TOE.round559TOEConvergenceCompilerLevel ≡ machineChecked
toeConvergenceCompilerMachineChecked = refl
