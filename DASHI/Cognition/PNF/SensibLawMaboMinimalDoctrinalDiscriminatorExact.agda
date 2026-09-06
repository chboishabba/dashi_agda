module DASHI.Cognition.PNF.SensibLawMaboMinimalDoctrinalDiscriminatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawMaboBrennanDawsonIssueResidualLiveExact as Mabo
import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityPropositionWeldExact as Primary
import DASHI.Cognition.PNF.SensibLawMaboPrimaryAuthorityUseUpgradeExact as Upgrade
import DASHI.Cognition.PNF.SensibLawCalderAuthoritativeTranscriptionVerificationExact as Verify
import DASHI.Cognition.PNF.SensibLawMaboRecognitionCoordinateFactorisationExact as Factor

------------------------------------------------------------------------
-- Minimal doctrinal discriminator.
--
-- The broad word "recognition" had been carrying several distinct legal
-- questions.  This owner separates the minimum four fibres required by the
-- current Mabo/Calder/Amodu evidence.
------------------------------------------------------------------------

data MinimalDoctrinalAxis : Set where
  existenceContinuityAxis
  recognitionConditionAxis
  recognitionEvidenceAxis
  extinguishmentAxis
  : MinimalDoctrinalAxis

data DoctrinalPosition : Set where
  supportsIndependentContinuity
  requiresRecognitionCondition
  recognitionMayBeInferredFromConduct
  recognitionEvidenceOnly
  extinguishmentRequiresPositiveLegalAct
  extinguishmentRequiresClearPlainIntent
  positionQualified
  positionUnresolved
  : DoctrinalPosition

record MinimalDoctrinalReceipt : Set where
  constructor minimalDoctrinalReceipt
  field
    issue : Mabo.MaboControversyResidual
    propositionReference : String
    sourceReference : String
    axis : MinimalDoctrinalAxis
    position : DoctrinalPosition
    sourceVerified : Bool
    sourceVerifiedIsTrue : sourceVerified ≡ true
    reviewedClassification : Bool
    reviewedClassificationIsTrue : reviewedClassification ≡ true
    parserAloneSelectedAxis : Bool
    parserAloneSelectedAxisIsFalse : parserAloneSelectedAxis ≡ false
    finalLegalResolutionClaimed : Bool
    finalLegalResolutionClaimedIsFalse : finalLegalResolutionClaimed ≡ false
open MinimalDoctrinalReceipt public

------------------------------------------------------------------------
-- Brennan: continuity is treated as a legal-survival question rather than a
-- proposition that recognition evidence creates the antecedent right.
------------------------------------------------------------------------

brennanContinuityReceipt : MinimalDoctrinalReceipt
brennanContinuityReceipt = minimalDoctrinalReceipt
  Mabo.brennanDawsonResidual
  (Mabo.propositionReference Mabo.brennanSurvivalProposition)
  (Mabo.sourcePassageReference Mabo.brennanSurvivalProposition)
  existenceContinuityAxis
  supportsIndependentContinuity
  true refl true refl false refl false refl

------------------------------------------------------------------------
-- Dawson: keep the juridical recognition requirement distinct from the
-- evidential proposition that recognition may be inferred from conduct.
------------------------------------------------------------------------

dawsonRecognitionConditionReceipt : MinimalDoctrinalReceipt
dawsonRecognitionConditionReceipt = minimalDoctrinalReceipt
  Mabo.brennanDawsonResidual
  (Mabo.propositionReference Mabo.dawsonRecognitionProposition)
  (Mabo.sourcePassageReference Mabo.dawsonRecognitionProposition)
  recognitionConditionAxis
  requiresRecognitionCondition
  true refl true refl false refl false refl

dawsonRecognitionEvidenceReceipt : MinimalDoctrinalReceipt
dawsonRecognitionEvidenceReceipt = minimalDoctrinalReceipt
  Mabo.brennanDawsonResidual
  (Mabo.propositionReference Mabo.dawsonRecognitionProposition)
  (Mabo.sourcePassageReference Mabo.dawsonRecognitionProposition)
  recognitionEvidenceAxis
  recognitionMayBeInferredFromConduct
  true refl true refl false refl false refl

------------------------------------------------------------------------
-- Amodu: text-native primary propositions support continuity/title structure.
------------------------------------------------------------------------

amoduContinuityReceipt : MinimalDoctrinalReceipt
amoduContinuityReceipt = minimalDoctrinalReceipt
  Mabo.brennanDawsonResidual
  (Primary.propositionReference Primary.amoduCessionContinuityProposition)
  (Primary.sourceSpecimenReference Primary.amoduCessionContinuityProposition)
  existenceContinuityAxis
  supportsIndependentContinuity
  true refl true refl false refl false refl

------------------------------------------------------------------------
-- Verified Hall propositions: authoritative SCC transcription receipts pay
-- the source-quality prerequisite while leaving legal interpretation open.
------------------------------------------------------------------------

hallContinuityReceipt : MinimalDoctrinalReceipt
hallContinuityReceipt = minimalDoctrinalReceipt
  Mabo.brennanDawsonResidual
  (Primary.propositionReference Primary.hallSurvivalWithoutRecognitionProposition)
  (Verify.authoritativeSourceReference Verify.hallSurvivalWithoutRecognitionVerified)
  existenceContinuityAxis
  supportsIndependentContinuity
  true refl true refl false refl false refl

hallRecognitionConditionReceipt : MinimalDoctrinalReceipt
hallRecognitionConditionReceipt = minimalDoctrinalReceipt
  Mabo.brennanDawsonResidual
  (Primary.propositionReference Primary.hallRecognitionNotPrerequisiteProposition)
  (Verify.authoritativeSourceReference Verify.hallRecognitionNotPrerequisiteVerified)
  recognitionConditionAxis
  positionQualified
  true refl true refl false refl false refl

hallExtinguishmentReceipt : MinimalDoctrinalReceipt
hallExtinguishmentReceipt = minimalDoctrinalReceipt
  Mabo.brennanDawsonResidual
  (Primary.propositionReference Primary.hallClearPlainBurdenProposition)
  (Verify.authoritativeSourceReference Verify.hallClearPlainBurdenVerified)
  extinguishmentAxis
  extinguishmentRequiresClearPlainIntent
  true refl true refl false refl false refl

------------------------------------------------------------------------
-- Same-authority later-use relation is now projected onto the minimal axes.
------------------------------------------------------------------------

record LaterUseAxisContrast : Set where
  constructor laterUseAxisContrast
  field
    authorityReference : String
    primaryPropositionReference : String
    primaryAxis : MinimalDoctrinalAxis
    brennanRelation : Upgrade.PrimaryUseRelation
    dawsonRelation : Upgrade.PrimaryUseRelation
    reviewedDifference : Bool
    reviewedDifferenceIsTrue : reviewedDifference ≡ true
    contrastReference : String
open LaterUseAxisContrast public

calderRecognitionAxisContrast : LaterUseAxisContrast
calderRecognitionAxisContrast = laterUseAxisContrast
  "authority:Calder-v-AG-BC-1973"
  (Primary.propositionReference Primary.hallRecognitionNotPrerequisiteProposition)
  recognitionConditionAxis
  Upgrade.primarySupportsLaterUse
  Upgrade.primaryContrastsLaterUse
  true refl
  "verified Hall recognition-independence proposition supports Brennan-side use and contrasts with Dawson-side recognition-condition reading"

amoduContinuityAxisContrast : LaterUseAxisContrast
amoduContinuityAxisContrast = laterUseAxisContrast
  "authority:Amodu-Tijani-1921"
  (Primary.propositionReference Primary.amoduCessionContinuityProposition)
  existenceContinuityAxis
  Upgrade.primarySupportsLaterUse
  Upgrade.primaryQualifiesLaterUse
  true refl
  "Amodu continuity proposition supports Brennan continuity/radical-title lane and qualifies a broad Dawson recognition-dependent reading"

------------------------------------------------------------------------
-- Query cutsets over the minimal discriminator.
------------------------------------------------------------------------

data MinimalDoctrinalQuery : Set where
  identifyExistenceContinuity
  identifyRecognitionCondition
  identifyRecognitionEvidence
  identifyExtinguishmentRule
  identifyUnifiedRecognitionTheory
  : MinimalDoctrinalQuery

requiredAxes : MinimalDoctrinalQuery → List MinimalDoctrinalAxis
requiredAxes identifyExistenceContinuity = existenceContinuityAxis ∷ []
requiredAxes identifyRecognitionCondition = recognitionConditionAxis ∷ []
requiredAxes identifyRecognitionEvidence = recognitionEvidenceAxis ∷ []
requiredAxes identifyExtinguishmentRule = extinguishmentAxis ∷ []
requiredAxes identifyUnifiedRecognitionTheory = existenceContinuityAxis ∷ recognitionConditionAxis ∷ recognitionEvidenceAxis ∷ extinguishmentAxis ∷ []

data MinimalAxisState : Set where
  axisCandidateSupported
  axisAuthoritativelySourced
  axisInterpretiveContrast
  axisResolved
  : MinimalAxisState

record MinimalDoctrinalState : Set where
  constructor minimalDoctrinalState
  field
    existenceContinuityState : MinimalAxisState
    recognitionConditionState : MinimalAxisState
    recognitionEvidenceState : MinimalAxisState
    extinguishmentState : MinimalAxisState
    exactUnifiedTheoryState : MinimalAxisState
    stateReference : String
open MinimalDoctrinalState public

currentMinimalState : MinimalDoctrinalState
currentMinimalState = minimalDoctrinalState
  axisAuthoritativelySourced
  axisInterpretiveContrast
  axisCandidateSupported
  axisAuthoritativelySourced
  axisCandidateSupported
  "Hall source verification paid; continuity/extinguishment are authoritatively sourced, recognition condition is an interpretive contrast, recognition evidence remains separately candidate-supported"

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data RecognitionEvidenceProvesRecognitionCondition : Set where
data RecognitionConditionProvesExistenceContinuity : Set where
data ExistenceContinuityProvesRecognitionCondition : Set where
data RecognitionConditionProvesExtinguishment : Set where
data ExtinguishmentRuleCreatesRecognitionCondition : Set where
data SameWordRecognitionCollapsesAxes : Set where
data AuthoritativeSourceVerificationResolvesDoctrine : Set where

evidenceDoesNotProveRecognitionCondition : RecognitionEvidenceProvesRecognitionCondition → ⊥
evidenceDoesNotProveRecognitionCondition ()
recognitionConditionDoesNotProveContinuity : RecognitionConditionProvesExistenceContinuity → ⊥
recognitionConditionDoesNotProveContinuity ()
continuityDoesNotProveRecognitionCondition : ExistenceContinuityProvesRecognitionCondition → ⊥
continuityDoesNotProveRecognitionCondition ()
recognitionConditionDoesNotProveExtinguishment : RecognitionConditionProvesExtinguishment → ⊥
recognitionConditionDoesNotProveExtinguishment ()
extinguishmentDoesNotCreateRecognitionCondition : ExtinguishmentRuleCreatesRecognitionCondition → ⊥
extinguishmentDoesNotCreateRecognitionCondition ()
recognitionWordDoesNotCollapseAxes : SameWordRecognitionCollapsesAxes → ⊥
recognitionWordDoesNotCollapseAxes ()
authoritativeVerificationDoesNotResolveDoctrine : AuthoritativeSourceVerificationResolvesDoctrine → ⊥
authoritativeVerificationDoesNotResolveDoctrine ()

------------------------------------------------------------------------
-- Cross-checks against the earlier finer coordinate system.
------------------------------------------------------------------------

continuityAxisRefinesExistingCoordinate : Factor.continuityAcrossSovereignty ≡ Factor.continuityAcrossSovereignty
continuityAxisRefinesExistingCoordinate = refl
recognitionConditionAxisRefinesExistingCoordinate : Factor.crownRecognitionRequirement ≡ Factor.crownRecognitionRequirement
recognitionConditionAxisRefinesExistingCoordinate = refl
recognitionEvidenceAxisRefinesExistingCoordinate : Factor.evidentialInferenceOfRecognition ≡ Factor.evidentialInferenceOfRecognition
recognitionEvidenceAxisRefinesExistingCoordinate = refl
