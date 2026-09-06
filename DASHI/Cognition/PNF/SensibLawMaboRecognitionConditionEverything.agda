module DASHI.Cognition.PNF.SensibLawMaboRecognitionConditionEverything where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboSovereigntyRecognitionRelationalBraidExact as Braid
import DASHI.Cognition.PNF.SensibLawMaboColonialSovereigntyCriticalResidualExact as Critical
import DASHI.Cognition.PNF.SensibLawMaboDawsonRecognitionConditionRefinementExact as Dawson
import DASHI.Cognition.PNF.SensibLawMaboDawsonRecognitionResidualPlannerExact as Planner
import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalDiscriminatorExact as Minimal
import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalCutsetExact as Cutset
import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalHyperfabricBridgeExact as Hyper
import DASHI.Cognition.PNF.SensibLawIssueIndexedAdjudicativeHyperfabricExact as Issue

------------------------------------------------------------------------
-- Focused recognition-condition + critical-sovereignty capstone.
------------------------------------------------------------------------

crownLegalPremiseIsCourtInternal :
  Critical.frame Critical.crownSovereigntyCourtPremise ≡ Critical.australianCourtInternalFrame
crownLegalPremiseIsCourtInternal = refl

indigenousCessionStatusIsIndependentFrame :
  Critical.frame Critical.sovereigntyNeverCededCriticalClaim ≡ Critical.indigenousSovereigntyFrame
indigenousCessionStatusIsIndependentFrame = refl

nativeTitleRecognitionDoesNotCloseSovereigntyRecognition :
  Critical.sovereigntyRecognitionClosed Critical.postMaboCriticalResidual ≡ false
nativeTitleRecognitionDoesNotCloseSovereigntyRecognition = refl

nativeTitleRecognitionDoesNotCloseLandRestitution :
  Critical.landRestitutionClosed Critical.postMaboCriticalResidual ≡ false
nativeTitleRecognitionDoesNotCloseLandRestitution = refl

nativeTitleRecognitionDoesNotCloseMaterialReparation :
  Critical.materialReparationClosed Critical.postMaboCriticalResidual ≡ false
nativeTitleRecognitionDoesNotCloseMaterialReparation = refl

landAndColonialityAxesRemainNonEraseable :
  Critical.landAxisEraseableAfterNativeTitleRecognition Critical.canonicalCriticalAxisBoundary ≡ false
landAndColonialityAxesRemainNonEraseable = refl

colonialityAxisRemainsNonEraseable :
  Critical.colonialityAxisEraseableAfterNativeTitleRecognition Critical.canonicalCriticalAxisBoundary ≡ false
colonialityAxisRemainsNonEraseable = refl

------------------------------------------------------------------------
-- Earlier `mere change of sovereignty` label retained only as a compatibility
-- theorem for the court-internal continuity rule, not as the preferred critical
-- description of colonisation.
------------------------------------------------------------------------

earlierMereLabelIsCompatibilityOnly :
  Critical.mereChangeLabelStatus ≡ Critical.retainedOnlyForCourtInternalCompatibility
earlierMereLabelIsCompatibilityOnly = refl

courtInternalTransitionAloneDoesNotEncodeExtinguishment :
  Braid.transitionEffect Braid.mereChangeOfSovereignty
  ≡ Braid.continuityNotDisplacedByTransitionAlone
courtInternalTransitionAloneDoesNotEncodeExtinguishment = refl

courtInternalContinuityRuleStillAllowsFurtherJuridicalActs :
  Braid.furtherJuridicalActMayAlterRights Braid.maboMereSovereigntyBoundary ≡ true
courtInternalContinuityRuleStillAllowsFurtherJuridicalActs = refl

------------------------------------------------------------------------
-- Dawson recognition-condition/evidence split.
------------------------------------------------------------------------

dawsonRecognitionConditionIsJuridical :
  Dawson.role Dawson.dawsonRecognitionConditionComponent ≡ Dawson.juridicalConditionRole
dawsonRecognitionConditionIsJuridical = refl

dawsonAcquiescenceIsEvidence :
  Dawson.role Dawson.dawsonAcquiescenceEvidenceComponent ≡ Dawson.evidenceModeRole
dawsonAcquiescenceIsEvidence = refl

dawsonConditionAndEvidenceUseDifferentAxes :
  Dawson.conditionAxis Dawson.dawsonConditionAcquiescenceSplit ≡ Minimal.recognitionConditionAxis
dawsonConditionAndEvidenceUseDifferentAxes = refl

dawsonEvidenceAxisIsSeparate :
  Dawson.evidenceAxis Dawson.dawsonConditionAcquiescenceSplit ≡ Minimal.recognitionEvidenceAxis
dawsonEvidenceAxisIsSeparate = refl

unifiedTheoryStillStopsAtRecognitionCondition :
  Cutset.firstResidual Minimal.identifyUnifiedRecognitionTheory Cutset.postHallVerificationCutset
  ≡ Cutset.recognitionConditionResidual
unifiedTheoryStillStopsAtRecognitionCondition = refl

recognitionConditionStillUsesAuthorityLook :
  Hyper.workKind Hyper.recognitionConditionHyperfabric ≡ Issue.lookWork
recognitionConditionStillUsesAuthorityLook = refl

recognitionEvidenceStillUsesEvidenceTest :
  Hyper.workKind Hyper.recognitionEvidenceHyperfabric ≡ Issue.testWork
recognitionEvidenceStillUsesEvidenceTest = refl

currentPlannerNeedsNoParserRerun : Planner.parserRerunRequired Planner.currentDawsonRecognitionPlan ≡ false
currentPlannerNeedsNoParserRerun = refl

currentPlannerDoesNotRequireJudsonYet : Planner.judsonRequiredNow Planner.currentDawsonRecognitionPlan ≡ false
currentPlannerDoesNotRequireJudsonYet = refl

------------------------------------------------------------------------
-- Intersectional/relational observer-source boundaries.
------------------------------------------------------------------------

affectedVoiceDoesNotEqualStateRecognition :
  Dawson.affectedVoiceEqualsStateRecognition Dawson.pluralRecognitionObserverBoundary ≡ false
affectedVoiceDoesNotEqualStateRecognition = refl

stateRecognitionDoesNotExhaustNormativeSource :
  Dawson.stateRecognitionExhaustsNormativeSource Dawson.pluralRecognitionObserverBoundary ≡ false
stateRecognitionDoesNotExhaustNormativeSource = refl

externalInterpretationDoesNotCreateCommunityAuthority :
  Dawson.externalInterpretationCreatesCommunityAuthority Dawson.pluralRecognitionObserverBoundary ≡ false
externalInterpretationDoesNotCreateCommunityAuthority = refl

------------------------------------------------------------------------
-- Critical repair non-substitution laws.
------------------------------------------------------------------------

nativeTitleRecognitionDoesNotProveSovereigntyRecognition : Critical.NativeTitleRecognitionProvesSovereigntyRecognition → ⊥
nativeTitleRecognitionDoesNotProveSovereigntyRecognition = Critical.nativeTitleDoesNotProveSovereigntyRecognition

nativeTitleRecognitionDoesNotRepairDispossession : Critical.NativeTitleRecognitionRepairsDispossession → ⊥
nativeTitleRecognitionDoesNotRepairDispossession = Critical.nativeTitleDoesNotRepairDispossessionByItself

apologyDoesNotEqualLandRestitution : Critical.FormalApologyEqualsLandRestitution → ⊥
apologyDoesNotEqualLandRestitution = Critical.apologyDoesNotEqualLandRestitution

politicalRecognitionDoesNotEqualLandReturn : Critical.PoliticalRecognitionEqualsLandReturn → ⊥
politicalRecognitionDoesNotEqualLandReturn = Critical.politicalRecognitionDoesNotEqualLandReturn

terraNulliusRejectionDoesNotCompleteDecolonisation : Critical.RejectionOfTerraNulliusCompletesDecolonisation → ⊥
terraNulliusRejectionDoesNotCompleteDecolonisation = Critical.terraNulliusRejectionDoesNotCompleteDecolonisation

courtPremiseDoesNotProveIndigenousCession : Critical.CrownLegalPremiseProvesIndigenousCession → ⊥
courtPremiseDoesNotProveIndigenousCession = Critical.crownPremiseDoesNotProveCession

courtPremiseDoesNotProveColonialLegitimacy : Critical.CrownLegalPremiseProvesColonialLegitimacy → ⊥
courtPremiseDoesNotProveColonialLegitimacy = Critical.crownPremiseDoesNotProveLegitimacy

------------------------------------------------------------------------
-- Existing recognition no-collapse laws.
------------------------------------------------------------------------

recognitionEvidenceDoesNotPayCondition : Dawson.RecognitionEvidencePaysJuridicalCondition → ⊥
recognitionEvidenceDoesNotPayCondition = Dawson.evidenceDoesNotPayCondition

recognitionConditionDoesNotCreateAntecedentRight : Dawson.RecognitionConditionCreatesAntecedentCommunityRight → ⊥
recognitionConditionDoesNotCreateAntecedentRight = Dawson.conditionDoesNotCreateAntecedentCommunityRight

governanceAnalogyDoesNotBecomeNativeTitleDoctrine : Braid.GovernanceRecognitionRuleIsNativeTitleDoctrine → ⊥
governanceAnalogyDoesNotBecomeNativeTitleDoctrine = Braid.governanceRecognitionDoesNotBecomeNativeTitleDoctrine

sweetgrassReciprocityDoesNotCreateHolding : Braid.SweetgrassReciprocityCreatesLegalHolding → ⊥
sweetgrassReciprocityDoesNotCreateHolding = Braid.sweetgrassReciprocityDoesNotCreateLegalHolding

moreRecognitionEvidenceDoesNotCloseCondition : Planner.MoreRecognitionEvidenceClosesRecognitionCondition → ⊥
moreRecognitionEvidenceDoesNotCloseCondition = Planner.evidenceDoesNotCloseConditionByItself

judsonIsNotCurrentPrecondition : Planner.JudsonMustBeResolvedBeforeInspectingDawsonRule → ⊥
judsonIsNotCurrentPrecondition = Planner.judsonIsNotCurrentPrecondition
