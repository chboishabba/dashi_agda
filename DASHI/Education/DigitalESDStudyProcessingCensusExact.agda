module DASHI.Education.DigitalESDStudyProcessingCensusExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

expectedERICMetadataCount : Nat
expectedERICMetadataCount = 43996

record StudyProcessingCensusReceipt : Set where
  constructor study-processing-census-receipt
  field
    receiptReference : String
    receiptSha256 : String
    metadataRecords : Nat
    genuinelyScreenedRecords : Nat
    includeProbableEligible : Nat
    verifiedFullTextArtifacts : Nat
    handedToSLR : Nat
    successfullyParsedBySLR : Nat
    reviewedCanonicalEvidence : Nat
    sourceAuditAdmissionComplete : Nat

    metadataCountMatchesExpected : Bool
    metadataCountMatchesExpectedIsTrue : metadataCountMatchesExpected ≡ true
    denominatorIntegrity : Bool
    denominatorIntegrityIsTrue : denominatorIntegrity ≡ true
    retainedSubsetOfScreened : Bool
    retainedSubsetOfScreenedIsTrue : retainedSubsetOfScreened ≡ true
    fullTextSubsetOfRetained : Bool
    fullTextSubsetOfRetainedIsTrue : fullTextSubsetOfRetained ≡ true
    handoffSubsetOfFullText : Bool
    handoffSubsetOfFullTextIsTrue : handoffSubsetOfFullText ≡ true
    parsedSubsetOfHandoff : Bool
    parsedSubsetOfHandoffIsTrue : parsedSubsetOfHandoff ≡ true
    reviewedSubsetOfParsed : Bool
    reviewedSubsetOfParsedIsTrue : reviewedSubsetOfParsed ≡ true
    admittedSubsetOfReviewed : Bool
    admittedSubsetOfReviewedIsTrue : admittedSubsetOfReviewed ≡ true

open StudyProcessingCensusReceipt public


------------------------------------------------------------------------
-- Per-study processing ledger beneath the aggregate census.
--
-- A row records observed stage membership explicitly.  Later stages do not
-- imply earlier stages by inference; the runtime must observe and reconcile
-- every coordinate and then prove containment booleans separately.
------------------------------------------------------------------------

record StudyProcessingRowReceipt : Set where
  constructor study-processing-row-receipt
  field
    sourceIdentityReference : String
    metadataRevisionReference : String
    rowReceiptReference : String

    authoritativeScreeningDecisionObserved : Bool
    retainedIncludeOrProbableObserved : Bool
    verifiedFullTextObserved : Bool
    textMaterialisationObserved : Bool
    slrHandoffObserved : Bool
    slrParseObserved : Bool
    reviewedCanonicalEvidenceObserved : Bool
    sourceAuditAdmissionObserved : Bool

    retainedImpliesScreenedObserved : Bool
    retainedImpliesScreenedObservedIsTrue :
      retainedImpliesScreenedObserved ≡ true

    fullTextImpliesRetainedObserved : Bool
    fullTextImpliesRetainedObservedIsTrue :
      fullTextImpliesRetainedObserved ≡ true

    materialisationImpliesFullTextObserved : Bool
    materialisationImpliesFullTextObservedIsTrue :
      materialisationImpliesFullTextObserved ≡ true

    handoffImpliesMaterialisationObserved : Bool
    handoffImpliesMaterialisationObservedIsTrue :
      handoffImpliesMaterialisationObserved ≡ true

    parseImpliesHandoffObserved : Bool
    parseImpliesHandoffObservedIsTrue :
      parseImpliesHandoffObserved ≡ true

    reviewImpliesParseObserved : Bool
    reviewImpliesParseObservedIsTrue :
      reviewImpliesParseObserved ≡ true

    admissionImpliesReviewObserved : Bool
    admissionImpliesReviewObservedIsTrue :
      admissionImpliesReviewObserved ≡ true

    laterStageInferredWithoutReceipt : Bool
    laterStageInferredWithoutReceiptIsFalse :
      laterStageInferredWithoutReceipt ≡ false

open StudyProcessingRowReceipt public

record StudyProcessingLedgerReceipt : Set where
  constructor study-processing-ledger-receipt
  field
    inputMetadataUniverseReference : String
    inputMetadataUniverseSha256 : String
    processingLedgerReference : String
    processingLedgerSha256 : String
    processingRowCount : Nat
    processingRowCountMatchesExpected :
      processingRowCount ≡ expectedERICMetadataCount

    everyMetadataRecordHasProcessingRow : Bool
    everyMetadataRecordHasProcessingRowIsTrue :
      everyMetadataRecordHasProcessingRow ≡ true

    stageContainmentCheckedPerRow : Bool
    stageContainmentCheckedPerRowIsTrue :
      stageContainmentCheckedPerRow ≡ true

    laterStageInferenceForbiddenPerRow : Bool
    laterStageInferenceForbiddenPerRowIsTrue :
      laterStageInferenceForbiddenPerRow ≡ true

open StudyProcessingLedgerReceipt public

record StudyProcessingCensusBoundary : Set where
  constructor study-processing-census-boundary
  field
    expectedMetadataUniversePinned : Bool
    expectedMetadataUniversePinnedIsTrue : expectedMetadataUniversePinned ≡ true
    requiresAuthoritativeDecisionField : Bool
    requiresAuthoritativeDecisionFieldIsTrue : requiresAuthoritativeDecisionField ≡ true
    triageStatusCountsAsDecision : Bool
    triageStatusCountsAsDecisionIsFalse : triageStatusCountsAsDecision ≡ false
    requiresStageContainment : Bool
    requiresStageContainmentIsTrue : requiresStageContainment ≡ true
    allowsLaterStageInference : Bool
    allowsLaterStageInferenceIsFalse : allowsLaterStageInference ≡ false
    verifiedFullTextMeansParsed : Bool
    verifiedFullTextMeansParsedIsFalse : verifiedFullTextMeansParsed ≡ false
    parsedMeansReviewed : Bool
    parsedMeansReviewedIsFalse : parsedMeansReviewed ≡ false
    reviewedMeansSourceAuditAdmission : Bool
    reviewedMeansSourceAuditAdmissionIsFalse : reviewedMeansSourceAuditAdmission ≡ false

open StudyProcessingCensusBoundary public

canonicalStudyProcessingCensusBoundary : StudyProcessingCensusBoundary
canonicalStudyProcessingCensusBoundary =
  study-processing-census-boundary
    true refl true refl false refl true refl false refl
    false refl false refl false refl

data MetadataPresenceCreatesScreeningDecision : Set where
data TriageStatusCreatesScreeningDecision : Set where
data CandidateAssessmentCreatesScreeningDecision : Set where
data VerifiedFullTextCreatesSLRParseReceipt : Set where
data SLRHandoffCreatesParseReceipt : Set where
data SLRParseCreatesReviewedEvidence : Set where
data ReviewedEvidenceCreatesSourceAuditAdmission : Set where
data SourceAuditAdmissionCreatesCorpusTruth : Set where
data LaterStageMayCreateEarlierStageWithoutReceipt : Set where
data MissingProcessingRowMayLeaveDenominator : Set where

metadataPresenceDoesNotCreateScreeningDecision :
  MetadataPresenceCreatesScreeningDecision → ⊥
metadataPresenceDoesNotCreateScreeningDecision ()

triageStatusDoesNotCreateScreeningDecision :
  TriageStatusCreatesScreeningDecision → ⊥
triageStatusDoesNotCreateScreeningDecision ()

candidateAssessmentDoesNotCreateScreeningDecision :
  CandidateAssessmentCreatesScreeningDecision → ⊥
candidateAssessmentDoesNotCreateScreeningDecision ()

verifiedFullTextDoesNotCreateSLRParseReceipt :
  VerifiedFullTextCreatesSLRParseReceipt → ⊥
verifiedFullTextDoesNotCreateSLRParseReceipt ()

slrHandoffDoesNotCreateParseReceipt :
  SLRHandoffCreatesParseReceipt → ⊥
slrHandoffDoesNotCreateParseReceipt ()

slrParseDoesNotCreateReviewedEvidence :
  SLRParseCreatesReviewedEvidence → ⊥
slrParseDoesNotCreateReviewedEvidence ()

reviewedEvidenceDoesNotCreateSourceAuditAdmission :
  ReviewedEvidenceCreatesSourceAuditAdmission → ⊥
reviewedEvidenceDoesNotCreateSourceAuditAdmission ()

sourceAuditAdmissionDoesNotCreateCorpusTruth :
  SourceAuditAdmissionCreatesCorpusTruth → ⊥
sourceAuditAdmissionDoesNotCreateCorpusTruth ()

laterStageDoesNotCreateEarlierStageWithoutReceipt :
  LaterStageMayCreateEarlierStageWithoutReceipt → ⊥
laterStageDoesNotCreateEarlierStageWithoutReceipt ()

missingProcessingRowDoesNotLeaveDenominator :
  MissingProcessingRowMayLeaveDenominator → ⊥
missingProcessingRowDoesNotLeaveDenominator ()
