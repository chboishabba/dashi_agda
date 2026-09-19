module DASHI.Education.DigitalESDTitleAbstractScreeningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- DURABLE TITLE / ABSTRACT SCREENING RECEIPT
--
-- This is the operational carrier for the real deduplicated bibliographic
-- corpus. It intentionally exists before AttributedSource / SourceAuditAdmission
-- because excluded and unresolved records must remain ledgered too.
------------------------------------------------------------------------

data ScreeningDecision : Set where
  include
  probable
  exclude
  unresolved
  : ScreeningDecision

data ScreeningReasonCode : Set where
  populationMismatch
  educationContextMismatch
  interventionOrTechnologyMismatch
  sustainabilityQuestionMismatch
  noEmpiricalStudy
  noRelevantReviewOrMethodRole
  insufficientTitleAbstractEvidence
  inaccessibleAbstract
  languageOutsideDeclaredScope
  publicationTypeOutsideDeclaredScope
  duplicateCandidate
  potentiallyRelevant
  requiresFullText
  otherScreeningReason
  : ScreeningReasonCode

data OptionalReference : Set where
  noReference : OptionalReference
  reference : String → OptionalReference

------------------------------------------------------------------------
-- Deduplication layers remain distinct.
------------------------------------------------------------------------

data DuplicateRelationKind : Set where
  metadataDuplicate
  publicationDuplicate
  reportFamilyDuplicate
  sameEmpiricalStudy
  : DuplicateRelationKind

record DuplicateRelationReceipt : Set where
  constructor duplicate-relation-receipt
  field
    leftSourceIdentityReference : String
    rightSourceIdentityReference : String
    relationKind : DuplicateRelationKind
    decisionReference : String
    reviewerOrProcessReference : String
    metadataEqualityCreatesStudyIdentity : Bool
    metadataEqualityCreatesStudyIdentityIsFalse :
      metadataEqualityCreatesStudyIdentity ≡ false

open DuplicateRelationReceipt public

------------------------------------------------------------------------
-- One durable decision per metadata revision/snapshot.
------------------------------------------------------------------------

record ScreeningDecisionReceipt : Set where
  constructor screening-decision-receipt
  field
    sourceIdentityReference : String
    metadataRevisionReference : String
    metadataSha256 : String
    titleAbstractSnapshotReference : String
    titleAbstractSnapshotSha256 : String

    screeningRubricVersion : String
    decision : ScreeningDecision
    reasonCodes : List ScreeningReasonCode
    freeTextReason : String

    reviewerOrModelReference : String
    processReference : String
    decisionTimestamp : String
    supersedesDecisionReference : OptionalReference

    exactMetadataSnapshotRetained : Bool
    exactMetadataSnapshotRetainedIsTrue :
      exactMetadataSnapshotRetained ≡ true

    exclusionOrAmbiguityRetained : Bool
    exclusionOrAmbiguityRetainedIsTrue :
      exclusionOrAmbiguityRetained ≡ true

    decisionCreatesSourceTruth : Bool
    decisionCreatesSourceTruthIsFalse :
      decisionCreatesSourceTruth ≡ false

    decisionCreatesSourceAuditAdmission : Bool
    decisionCreatesSourceAuditAdmissionIsFalse :
      decisionCreatesSourceAuditAdmission ≡ false

    decisionRaisesClaimCeiling : Bool
    decisionRaisesClaimCeilingIsFalse :
      decisionRaisesClaimCeiling ≡ false

open ScreeningDecisionReceipt public

------------------------------------------------------------------------
-- Ledger receipt over the entire screened input universe.
------------------------------------------------------------------------

record ScreeningLedgerReceipt : Set where
  constructor screening-ledger-receipt
  field
    inputDeduplicatedSetReference : String
    inputDeduplicatedSetSha256 : String
    screeningRubricReference : String
    screeningRubricVersion : String
    decisionLedgerReference : String
    decisionLedgerSha256 : String

    inputRecordCountReference : String
    includeCountReference : String
    probableCountReference : String
    excludeCountReference : String
    unresolvedCountReference : String

    everyInputRecordRetainedInLedger : Bool
    everyInputRecordRetainedInLedgerIsTrue :
      everyInputRecordRetainedInLedger ≡ true

    exclusionsRetained : Bool
    exclusionsRetainedIsTrue : exclusionsRetained ≡ true

    ambiguitiesRetained : Bool
    ambiguitiesRetainedIsTrue : ambiguitiesRetained ≡ true

    supersessionAppendOnly : Bool
    supersessionAppendOnlyIsTrue : supersessionAppendOnly ≡ true

    screeningCreatesEvidenceTruth : Bool
    screeningCreatesEvidenceTruthIsFalse :
      screeningCreatesEvidenceTruth ≡ false

    screeningCreatesSourceAuditAdmission : Bool
    screeningCreatesSourceAuditAdmissionIsFalse :
      screeningCreatesSourceAuditAdmission ≡ false

open ScreeningLedgerReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ScreeningDecisionCreatesSourceTruth : Set where
data ScreeningDecisionCreatesSourceAuditAdmission : Set where
data ScreeningDecisionRaisesClaimCeiling : Set where
data MetadataDuplicateCreatesSameEmpiricalStudy : Set where
data PublicationDuplicateCreatesSameEmpiricalStudy : Set where
data ReportFamilyDuplicateCreatesSameEmpiricalStudy : Set where
data ExclusionMayBeDiscardedWithoutReceipt : Set where
data UnresolvedMayBeSilentlyExcluded : Set where
data ScreeningScoreCreatesSourceQuality : Set where

screeningDecisionDoesNotCreateSourceTruth :
  ScreeningDecisionCreatesSourceTruth → ⊥
screeningDecisionDoesNotCreateSourceTruth ()

screeningDecisionDoesNotCreateSourceAuditAdmission :
  ScreeningDecisionCreatesSourceAuditAdmission → ⊥
screeningDecisionDoesNotCreateSourceAuditAdmission ()

screeningDecisionDoesNotRaiseClaimCeiling :
  ScreeningDecisionRaisesClaimCeiling → ⊥
screeningDecisionDoesNotRaiseClaimCeiling ()

metadataDuplicateDoesNotCreateSameEmpiricalStudy :
  MetadataDuplicateCreatesSameEmpiricalStudy → ⊥
metadataDuplicateDoesNotCreateSameEmpiricalStudy ()

publicationDuplicateDoesNotCreateSameEmpiricalStudy :
  PublicationDuplicateCreatesSameEmpiricalStudy → ⊥
publicationDuplicateDoesNotCreateSameEmpiricalStudy ()

reportFamilyDuplicateDoesNotCreateSameEmpiricalStudy :
  ReportFamilyDuplicateCreatesSameEmpiricalStudy → ⊥
reportFamilyDuplicateDoesNotCreateSameEmpiricalStudy ()

exclusionMayNotBeDiscardedWithoutReceipt :
  ExclusionMayBeDiscardedWithoutReceipt → ⊥
exclusionMayNotBeDiscardedWithoutReceipt ()

unresolvedMayNotBeSilentlyExcluded :
  UnresolvedMayBeSilentlyExcluded → ⊥
unresolvedMayNotBeSilentlyExcluded ()

screeningScoreDoesNotCreateSourceQuality :
  ScreeningScoreCreatesSourceQuality → ⊥
screeningScoreDoesNotCreateSourceQuality ()

record ScreeningBoundary : Set where
  constructor screening-boundary
  field
    fourWayDecisionSurface : Bool
    fourWayDecisionSurfaceIsTrue : fourWayDecisionSurface ≡ true

    exactMetadataRevisionRetained : Bool
    exactMetadataRevisionRetainedIsTrue :
      exactMetadataRevisionRetained ≡ true

    everyExclusionRetained : Bool
    everyExclusionRetainedIsTrue : everyExclusionRetained ≡ true

    everyAmbiguityRetained : Bool
    everyAmbiguityRetainedIsTrue : everyAmbiguityRetained ≡ true

    duplicateLayersRemainDistinct : Bool
    duplicateLayersRemainDistinctIsTrue :
      duplicateLayersRemainDistinct ≡ true

    decisionsAreAppendOnlySupersedable : Bool
    decisionsAreAppendOnlySupersedableIsTrue :
      decisionsAreAppendOnlySupersedable ≡ true

    screeningIsAdmissionAuthority : Bool
    screeningIsAdmissionAuthorityIsFalse :
      screeningIsAdmissionAuthority ≡ false

open ScreeningBoundary public

canonicalScreeningBoundary : ScreeningBoundary
canonicalScreeningBoundary =
  screening-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl

screeningReading : String
screeningReading =
  "Digital-ESD title/abstract screening is a durable append-only decision ledger over the exact deduplicated metadata revision. Each source keeps its metadata hash, title/abstract snapshot hash, rubric version, include/probable/exclude/unresolved decision, reason codes, reviewer/model/process reference, timestamp and explicit supersession link. Excluded and unresolved records remain first-class review artifacts. Metadata duplicate, publication duplicate, report-family duplicate and same empirical study are distinct relations. Screening neither creates source truth, raises a claim ceiling nor constructs SourceAuditAdmission."
