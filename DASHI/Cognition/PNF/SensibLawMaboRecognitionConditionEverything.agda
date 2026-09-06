module DASHI.Cognition.PNF.SensibLawMaboRecognitionConditionEverything where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboSovereigntyRecognitionRelationalBraidExact as Braid
import DASHI.Cognition.PNF.SensibLawMaboDawsonRecognitionConditionRefinementExact as Dawson
import DASHI.Cognition.PNF.SensibLawMaboDawsonRecognitionResidualPlannerExact as Planner
import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalDiscriminatorExact as Minimal
import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalCutsetExact as Cutset
import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalHyperfabricBridgeExact as Hyper
import DASHI.Cognition.PNF.SensibLawIssueIndexedAdjudicativeHyperfabricExact as Issue

------------------------------------------------------------------------
-- Focused recognition-condition capstone.
------------------------------------------------------------------------

mereSovereigntyChangeDoesNotEncodeExtinguishment :
  Braid.transitionEffect Braid.mereChangeOfSovereignty
  ≡ Braid.continuityNotDisplacedByTransitionAlone
mereSovereigntyChangeDoesNotEncodeExtinguishment = refl

mereSovereigntyBoundaryStillAllowsFurtherJuridicalChange :
  Braid.furtherJuridicalActMayAlterRights Braid.maboMereSovereigntyBoundary ≡ true
mereSovereigntyBoundaryStillAllowsFurtherJuridicalChange = refl

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
-- No-collapse laws.
------------------------------------------------------------------------

recognitionEvidenceDoesNotPayCondition : Dawson.RecognitionEvidencePaysJuridicalCondition → ⊥
recognitionEvidenceDoesNotPayCondition = Dawson.evidenceDoesNotPayCondition

recognitionConditionDoesNotCreateAntecedentRight : Dawson.RecognitionConditionCreatesAntecedentCommunityRight → ⊥
recognitionConditionDoesNotCreateAntecedentRight = Dawson.conditionDoesNotCreateAntecedentCommunityRight

sovereigntyChangeAloneDoesNotExtinguish : Braid.SovereigntyChangeAloneExtinguishesAntecedentRight → ⊥
sovereigntyChangeAloneDoesNotExtinguish = Braid.sovereigntyChangeAloneDoesNotEncodeExtinguishment

governanceAnalogyDoesNotBecomeNativeTitleDoctrine : Braid.GovernanceRecognitionRuleIsNativeTitleDoctrine → ⊥
governanceAnalogyDoesNotBecomeNativeTitleDoctrine = Braid.governanceRecognitionDoesNotBecomeNativeTitleDoctrine

sweetgrassReciprocityDoesNotCreateHolding : Braid.SweetgrassReciprocityCreatesLegalHolding → ⊥
sweetgrassReciprocityDoesNotCreateHolding = Braid.sweetgrassReciprocityDoesNotCreateLegalHolding

moreRecognitionEvidenceDoesNotCloseCondition : Planner.MoreRecognitionEvidenceClosesRecognitionCondition → ⊥
moreRecognitionEvidenceDoesNotCloseCondition = Planner.evidenceDoesNotCloseConditionByItself

judsonIsNotCurrentPrecondition : Planner.JudsonMustBeResolvedBeforeInspectingDawsonRule → ⊥
judsonIsNotCurrentPrecondition = Planner.judsonIsNotCurrentPrecondition
