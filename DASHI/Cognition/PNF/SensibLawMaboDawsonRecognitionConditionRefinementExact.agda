module DASHI.Cognition.PNF.SensibLawMaboDawsonRecognitionConditionRefinementExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboBrennanDawsonIssueResidualLiveExact as Mabo
import DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalDiscriminatorExact as Minimal
import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityUseUpgradeExact as Upgrade
import DASHI.Cognition.PNF.SensibLawMaboSovereigntyRecognitionRelationalBraidExact as Relational
import DASHI.Governance.RevolutionaryPracticeBraid as Braid

------------------------------------------------------------------------
-- Dawson recognition architecture.
--
-- This is a reviewed decomposition of the already-owned Dawson recognition
-- proposition.  It separates the alleged juridical condition from the factual
-- means by which recognition/acceptance may be evidenced.
------------------------------------------------------------------------

data DawsonRecognitionComponent : Set where
  preExistingInterestCarrier : DawsonRecognitionComponent
  newSovereignRecognitionOrAcceptanceCondition : DawsonRecognitionComponent
  noGeneralRecognitionPresumption : DawsonRecognitionComponent
  factSpecificRecognitionDetermination : DawsonRecognitionComponent
  acquiescenceAsRecognitionEvidence : DawsonRecognitionComponent
  continuedOccupationAsRecognitionEvidence : DawsonRecognitionComponent
  crownConductAsRecognitionEvidence : DawsonRecognitionComponent


data ComponentRole : Set where
  antecedentObjectRole : ComponentRole
  juridicalConditionRole : ComponentRole
  antiPresumptionRuleRole : ComponentRole
  adjudicativeFactQuestionRole : ComponentRole
  evidenceModeRole : ComponentRole


componentRole : DawsonRecognitionComponent → ComponentRole
componentRole preExistingInterestCarrier = antecedentObjectRole
componentRole newSovereignRecognitionOrAcceptanceCondition = juridicalConditionRole
componentRole noGeneralRecognitionPresumption = antiPresumptionRuleRole
componentRole factSpecificRecognitionDetermination = adjudicativeFactQuestionRole
componentRole acquiescenceAsRecognitionEvidence = evidenceModeRole
componentRole continuedOccupationAsRecognitionEvidence = evidenceModeRole
componentRole crownConductAsRecognitionEvidence = evidenceModeRole

record ReviewedDawsonComponent : Set where
  constructor reviewedDawsonComponent
  field
    component : DawsonRecognitionComponent
    sourcePropositionReference : String
    reviewedSummary : String
    role : ComponentRole
    roleExact : role ≡ componentRole component
    sourceAttributionReviewed : Bool
    sourceAttributionReviewedIsTrue : sourceAttributionReviewed ≡ true
    parserAloneDerivedComponent : Bool
    parserAloneDerivedComponentIsFalse : parserAloneDerivedComponent ≡ false
    finalDoctrinalAdjudicationClaimed : Bool
    finalDoctrinalAdjudicationClaimedIsFalse : finalDoctrinalAdjudicationClaimed ≡ false
open ReviewedDawsonComponent public

dawsonRecognitionConditionComponent : ReviewedDawsonComponent
dawsonRecognitionConditionComponent = reviewedDawsonComponent
  newSovereignRecognitionOrAcceptanceCondition
  (Mabo.propositionReference Mabo.dawsonRecognitionProposition)
  "reviewed decomposition: Dawson treats recognition or acceptance by the new sovereign as the juridically relevant condition for continued legal effect in his sovereignty-change analysis"
  juridicalConditionRole refl true refl false refl false refl

dawsonNoPresumptionComponent : ReviewedDawsonComponent
dawsonNoPresumptionComponent = reviewedDawsonComponent
  noGeneralRecognitionPresumption
  (Mabo.propositionReference Mabo.dawsonRecognitionProposition)
  "reviewed decomposition: recognition/acceptance is treated as fact-specific rather than governed by a universal presumption for or against recognition"
  antiPresumptionRuleRole refl true refl false refl false refl

dawsonAcquiescenceEvidenceComponent : ReviewedDawsonComponent
dawsonAcquiescenceEvidenceComponent = reviewedDawsonComponent
  acquiescenceAsRecognitionEvidence
  (Mabo.propositionReference Mabo.dawsonRecognitionProposition)
  "reviewed decomposition: Crown acquiescence is treated as one evidential route by which recognition may be inferred"
  evidenceModeRole refl true refl false refl false refl

dawsonOccupationEvidenceComponent : ReviewedDawsonComponent
dawsonOccupationEvidenceComponent = reviewedDawsonComponent
  continuedOccupationAsRecognitionEvidence
  (Mabo.propositionReference Mabo.dawsonRecognitionProposition)
  "reviewed decomposition: continued undisturbed occupation/use may contribute evidence relevant to recognition"
  evidenceModeRole refl true refl false refl false refl

------------------------------------------------------------------------
-- Condition versus evidence.
------------------------------------------------------------------------

record DawsonRecognitionConditionEvidenceSplit : Set where
  constructor dawsonRecognitionConditionEvidenceSplit
  field
    juridicalCondition : ReviewedDawsonComponent
    evidenceRoute : ReviewedDawsonComponent
    conditionAxis : Minimal.MinimalDoctrinalAxis
    conditionAxisExact : conditionAxis ≡ Minimal.recognitionConditionAxis
    evidenceAxis : Minimal.MinimalDoctrinalAxis
    evidenceAxisExact : evidenceAxis ≡ Minimal.recognitionEvidenceAxis
    sameSourceProposition : Bool
    sameSourcePropositionIsTrue : sameSourceProposition ≡ true
    rolesRemainDistinct : Bool
    rolesRemainDistinctIsTrue : rolesRemainDistinct ≡ true
    splitReference : String
open DawsonRecognitionConditionEvidenceSplit public

dawsonConditionAcquiescenceSplit : DawsonRecognitionConditionEvidenceSplit
dawsonConditionAcquiescenceSplit = dawsonRecognitionConditionEvidenceSplit
  dawsonRecognitionConditionComponent
  dawsonAcquiescenceEvidenceComponent
  Minimal.recognitionConditionAxis refl
  Minimal.recognitionEvidenceAxis refl
  true refl true refl
  "same Dawson source proposition is decomposed into a juridical recognition condition and a distinct evidential route via acquiescence"

------------------------------------------------------------------------
-- The 'recognition creates the right' over-reading is blocked.
------------------------------------------------------------------------

data RightObjectStage : Set where
  antecedentCommunityNormativeRelation : RightObjectStage
  commonLawLegalRecognitionRelation : RightObjectStage
  crownRecognitionEvidenceState : RightObjectStage
  extinguishedState : RightObjectStage


record DawsonSourceCreationBoundary : Set where
  constructor dawsonSourceCreationBoundary
  field
    antecedentObject : RightObjectStage
    legalRecognitionLayer : RightObjectStage
    evidenceLayer : RightObjectStage
    crownRecognitionCreatesAntecedentObject : Bool
    crownRecognitionCreatesAntecedentObjectIsFalse : crownRecognitionCreatesAntecedentObject ≡ false
    crownRecognitionMayConditionLegalEffectInDawsonModel : Bool
    crownRecognitionMayConditionLegalEffectInDawsonModelIsTrue : crownRecognitionMayConditionLegalEffectInDawsonModel ≡ true
    evidenceMaySupportFindingOfRecognition : Bool
    evidenceMaySupportFindingOfRecognitionIsTrue : evidenceMaySupportFindingOfRecognition ≡ true
    boundaryReference : String
open DawsonSourceCreationBoundary public

dawsonSourceCreationBoundary : DawsonSourceCreationBoundary
dawsonSourceCreationBoundary = dawsonSourceCreationBoundary
  antecedentCommunityNormativeRelation
  commonLawLegalRecognitionRelation
  crownRecognitionEvidenceState
  false refl true refl true refl
  "representation firewall: Dawson's recognition condition is modelled as a condition on legal effect/recognition, not as creation ex nihilo of the antecedent Indigenous normative relation"

------------------------------------------------------------------------
-- Relational/intersectional braid: affected voice and state recognition are
-- different observer/source positions.  This is a formal representation rule,
-- not a doctrinal holding imported from Sweetgrass or governance theory.
------------------------------------------------------------------------

data RecognitionObserverPosition : Set where
  affectedCommunitySelfArticulation : RecognitionObserverPosition
  crownOrStateRecognition : RecognitionObserverPosition
  judicialRecognition : RecognitionObserverPosition
  externalAcademicInterpretation : RecognitionObserverPosition


record PluralRecognitionObserverBoundary : Set where
  constructor pluralRecognitionObserverBoundary
  field
    affectedVoice : RecognitionObserverPosition
    stateRecognition : RecognitionObserverPosition
    judicialRecognition : RecognitionObserverPosition
    affectedVoiceEqualsStateRecognition : Bool
    affectedVoiceEqualsStateRecognitionIsFalse : affectedVoiceEqualsStateRecognition ≡ false
    stateRecognitionExhaustsNormativeSource : Bool
    stateRecognitionExhaustsNormativeSourceIsFalse : stateRecognitionExhaustsNormativeSource ≡ false
    externalInterpretationCreatesCommunityAuthority : Bool
    externalInterpretationCreatesCommunityAuthorityIsFalse : externalInterpretationCreatesCommunityAuthority ≡ false
    boundaryReference : String
open PluralRecognitionObserverBoundary public

pluralRecognitionObserverBoundary : PluralRecognitionObserverBoundary
pluralRecognitionObserverBoundary = pluralRecognitionObserverBoundary
  affectedCommunitySelfArticulation
  crownOrStateRecognition
  judicialRecognition
  false refl false refl false refl
  "intersectional/relational representation boundary: affected-community articulation, state recognition and judicial recognition are distinct observer/source positions"

affectedVoicePracticeRemainsExplicit : Braid.PrefigurativePractice
affectedVoicePracticeRemainsExplicit = Braid.affectedVoicePractice

------------------------------------------------------------------------
-- Relation to the verified Hall/Amodu contrasts.
------------------------------------------------------------------------

dawsonConditionAxisReceipt : Minimal.MinimalDoctrinalReceipt
dawsonConditionAxisReceipt = Minimal.dawsonRecognitionConditionReceipt

dawsonEvidenceAxisReceipt : Minimal.MinimalDoctrinalReceipt
dawsonEvidenceAxisReceipt = Minimal.dawsonRecognitionEvidenceReceipt

hallContrastTargetsConditionNotEvidence :
  Minimal.primaryAxis Minimal.calderRecognitionAxisContrast ≡ Minimal.recognitionConditionAxis
hallContrastTargetsConditionNotEvidence = refl

amoduContinuityQualifiesRecognitionDependentReading :
  Minimal.dawsonRelation Minimal.amoduContinuityAxisContrast ≡ Upgrade.primaryQualifiesLaterUse
amoduContinuityQualifiesRecognitionDependentReading = refl

mereSovereigntyChangeStillNotExtinguishment :
  Relational.transitionEffect Relational.mereChangeOfSovereignty ≡ Relational.continuityNotDisplacedByTransitionAlone
mereSovereigntyChangeStillNotExtinguishment = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data RecognitionEvidencePaysJuridicalCondition : Set where
data RecognitionConditionCreatesAntecedentCommunityRight : Set where
data NoPresumptionMeansNoRecognitionCondition : Set where
data FactSpecificRecognitionMeansPureJudicialDiscretion : Set where
data StateRecognitionExhaustsIndigenousNormativeSource : Set where
data AffectedCommunityVoiceAutomaticallyDeterminesCommonLawHolding : Set where

evidenceDoesNotPayCondition : RecognitionEvidencePaysJuridicalCondition → ⊥
evidenceDoesNotPayCondition ()
conditionDoesNotCreateAntecedentCommunityRight : RecognitionConditionCreatesAntecedentCommunityRight → ⊥
conditionDoesNotCreateAntecedentCommunityRight ()
noPresumptionDoesNotEraseCondition : NoPresumptionMeansNoRecognitionCondition → ⊥
noPresumptionDoesNotEraseCondition ()
factSpecificDoesNotMeanUnboundedDiscretion : FactSpecificRecognitionMeansPureJudicialDiscretion → ⊥
factSpecificDoesNotMeanUnboundedDiscretion ()
stateRecognitionDoesNotExhaustIndigenousSource : StateRecognitionExhaustsIndigenousNormativeSource → ⊥
stateRecognitionDoesNotExhaustIndigenousSource ()
affectedVoiceDoesNotAutoDetermineHolding : AffectedCommunityVoiceAutomaticallyDeterminesCommonLawHolding → ⊥
affectedVoiceDoesNotAutoDetermineHolding ()
