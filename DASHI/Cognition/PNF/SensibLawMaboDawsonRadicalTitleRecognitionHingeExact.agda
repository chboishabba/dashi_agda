module DASHI.Cognition.PNF.SensibLawMaboDawsonRadicalTitleRecognitionHingeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboTwoLegalOrderFibreExact as TwoOrder
import DASHI.Cognition.PNF.SensibLawMaboDawsonRecognitionConditionRefinementExact as Dawson
import DASHI.Cognition.PNF.SensibLawMaboBrennanDawsonIssueResidualLiveExact as Mabo
import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityPropositionWeldExact as Primary

------------------------------------------------------------------------
-- Dawson radical-title -> recognition-condition hinge.
--
-- The exact Dawson primary fixture directly supports recognition as inferable
-- from all the facts, including acquiescence/continued undisturbed occupation.
-- It does not directly state that Crown radical title logically entails a
-- constitutive recognition condition. Candidate intermediate premises therefore
-- carry explicit source-status tags.
------------------------------------------------------------------------

data HingeSourceStatus : Set where
  directPrimaryText
  reviewedDoctrinalInference
  secondaryInterpretation
  unresolvedBridge
  : HingeSourceStatus

data HingePremiseKind : Set where
  crownSovereigntyReordersMunicipalLegalRelations
  radicalTitleStructuresCrownMunicipalPropertyOrder
  continuingInterestRequiresNewSovereignRecognition
  recognitionConditionMediatesMunicipalLegalEffect
  recognitionMayBeInferredFromFacts
  acquiescenceMayEvidenceRecognition
  continuedOccupationMayEvidenceRecognition
  : HingePremiseKind

record DawsonHingePremise : Set where
  constructor dawsonHingePremise
  field
    premise : HingePremiseKind
    sourceStatus : HingeSourceStatus
    sourceReference : String
    propositionSummary : String
    directlyParserObservedSemanticRule : Bool
    directlyParserObservedSemanticRuleIsFalse : directlyParserObservedSemanticRule ≡ false
    finalHoldingClaimed : Bool
    finalHoldingClaimedIsFalse : finalHoldingClaimed ≡ false
open DawsonHingePremise public

recognitionInferencePrimary : DawsonHingePremise
recognitionInferencePrimary = dawsonHingePremise
  recognitionMayBeInferredFromFacts
  directPrimaryText
  (Mabo.sourcePassageReference Mabo.dawsonRecognitionProposition)
  "Dawson primary passage: recognition of pre-existing interests by the Crown may be a matter of inference from all the facts"
  false refl false refl

acquiescenceEvidencePrimary : DawsonHingePremise
acquiescenceEvidencePrimary = dawsonHingePremise
  acquiescenceMayEvidenceRecognition
  directPrimaryText
  (Mabo.sourcePassageReference Mabo.dawsonRecognitionProposition)
  "Dawson primary passage expressly includes acquiescence among the facts from which Crown recognition may be inferred"
  false refl false refl

continuedOccupationEvidencePrimary : DawsonHingePremise
continuedOccupationEvidencePrimary = dawsonHingePremise
  continuedOccupationMayEvidenceRecognition
  directPrimaryText
  (Mabo.sourcePassageReference Mabo.dawsonRecognitionProposition)
  "Dawson primary passage: continued undisturbed native occupation/use after sovereignty may found a conclusion of Crown recognition"
  false refl false refl

radicalTitleRecognitionMediationCandidate : DawsonHingePremise
radicalTitleRecognitionMediationCandidate = dawsonHingePremise
  recognitionConditionMediatesMunicipalLegalEffect
  unresolvedBridge
  "DASHI/SensibLaw residual: CrownRadicalTitle -> ? -> DawsonRecognitionCondition"
  "candidate intermediate premise: within Dawson's municipal-law model, recognition by the new sovereign mediates continuing legal effect of antecedent interests; exact radical-title derivation remains unresolved"
  false refl false refl

continuingInterestRecognitionRequirementCandidate : DawsonHingePremise
continuingInterestRecognitionRequirementCandidate = dawsonHingePremise
  continuingInterestRequiresNewSovereignRecognition
  reviewedDoctrinalInference
  "reviewed Dawson recognition-condition decomposition; proposition-level primary derivation still to be isolated"
  "reviewed doctrinal inference: Dawson's account treats new-sovereign recognition/acceptance as juridically relevant to continuing municipal legal effect"
  false refl false refl

------------------------------------------------------------------------
-- Contrast with Brennan/Amodu continuity structure.
------------------------------------------------------------------------

data ContinuityModelKind : Set where
  antecedentRightsBurdenRadicalTitle
  recognitionMediatedMunicipalContinuity
  communalRightLimitsRadicalTitle
  : ContinuityModelKind

record ContinuityModelReceipt : Set where
  constructor continuityModelReceipt
  field
    model : ContinuityModelKind
    sourceStatus : HingeSourceStatus
    sourceReference : String
    summary : String
open ContinuityModelReceipt public

brennanContinuityModel : ContinuityModelReceipt
brennanContinuityModel = continuityModelReceipt
  antecedentRightsBurdenRadicalTitle
  directPrimaryText
  (Mabo.sourcePassageReference Mabo.brennanSurvivalProposition)
  "Brennan: antecedent Indigenous rights/interests survive sovereignty and constitute a burden on Crown radical title"

amoduRadicalTitleModel : ContinuityModelReceipt
amoduRadicalTitleModel = continuityModelReceipt
  communalRightLimitsRadicalTitle
  directPrimaryText
  (Primary.sourcePassageReference Primary.amoduUsufructRadicalTitleProposition)
  "Amodu: communal usufructuary title qualifies radical title and may reduce sovereign radical right to comparatively limited administrative interference"

dawsonRecognitionMediatedModel : ContinuityModelReceipt
dawsonRecognitionMediatedModel = continuityModelReceipt
  recognitionMediatedMunicipalContinuity
  reviewedDoctrinalInference
  (Mabo.sourcePassageReference Mabo.dawsonRecognitionProposition)
  "Dawson reviewed model: continuing municipal legal effect is mediated by Crown recognition/acceptance; direct radical-title derivation remains the live hinge"

------------------------------------------------------------------------
-- Exact current hinge state.
------------------------------------------------------------------------

data HingeClosure : Set where
  sourceMapped
  partiallyIdentified
  unresolvedDoctrinalBridge
  closedDoctrinalBridge
  : HingeClosure

record DawsonRadicalTitleRecognitionHinge : Set where
  constructor dawsonRadicalTitleRecognitionHinge
  field
    sourceNode : TwoOrder.LegalOrderNode
    targetNode : TwoOrder.LegalOrderNode
    bridgeStatus : TwoOrder.CrossOrderBridgeStatus
    closure : HingeClosure
    directRecognitionEvidenceMapped : Bool
    directRecognitionEvidenceMappedIsTrue : directRecognitionEvidenceMapped ≡ true
    radicalTitleEntailmentProved : Bool
    radicalTitleEntailmentProvedIsFalse : radicalTitleEntailmentProved ≡ false
    nextQuestion : String
open DawsonRadicalTitleRecognitionHinge public

currentDawsonHinge : DawsonRadicalTitleRecognitionHinge
currentDawsonHinge = dawsonRadicalTitleRecognitionHinge
  TwoOrder.crownRadicalTitle
  TwoOrder.crownRecognitionCondition
  (TwoOrder.status TwoOrder.radicalTitleToRecognitionCondition)
  unresolvedDoctrinalBridge
  true refl
  false refl
  "Identify the proposition, if any, by which Dawson moves from Crown radical title/sovereignty to a juridical requirement of Crown recognition for continued municipal legal effect; do not substitute acquiescence evidence for that missing premise"

currentBridgeRemainsContested :
  bridgeStatus currentDawsonHinge ≡ TwoOrder.contestedCourtInternalBridge
currentBridgeRemainsContested = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data RadicalTitleAloneEntailsRecognitionCondition : Set where
data RecognitionEvidenceEntailsConstitutiveRecognitionCondition : Set where
data AcquiescenceCreatesAntecedentIndigenousInterest : Set where
data ReviewedInferenceEqualsDirectPrimaryHolding : Set where
data BrennanContinuityEqualsDawsonRecognitionMediation : Set where

radicalTitleAloneDoesNotCloseHinge : RadicalTitleAloneEntailsRecognitionCondition → ⊥
radicalTitleAloneDoesNotCloseHinge ()

recognitionEvidenceDoesNotEntailCondition : RecognitionEvidenceEntailsConstitutiveRecognitionCondition → ⊥
recognitionEvidenceDoesNotEntailCondition ()

acquiescenceDoesNotCreateAntecedentInterest : AcquiescenceCreatesAntecedentIndigenousInterest → ⊥
acquiescenceDoesNotCreateAntecedentInterest ()

reviewedInferenceDoesNotBecomePrimaryHolding : ReviewedInferenceEqualsDirectPrimaryHolding → ⊥
reviewedInferenceDoesNotBecomePrimaryHolding ()

brennanAndDawsonModelsDoNotAutoCollapse : BrennanContinuityEqualsDawsonRecognitionMediation → ⊥
brennanAndDawsonModelsDoNotAutoCollapse ()
