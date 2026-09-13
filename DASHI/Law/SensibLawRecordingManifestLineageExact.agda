module DASHI.Law.SensibLawRecordingManifestLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- RECORDING / MANIFEST / COPY / TRANSCRIPT / SUBMISSION LINEAGE
--
-- DASHI-original provenance boundary.
--
-- The Recordings and Transcriptions spreadsheet is treated as an index of
-- Google Recorder captures.  An index row, the underlying recording, a cloud
-- copy, a downloaded local copy, a transcript/archive derivative and a
-- QCAT-submitted derivative are constructor-distinct carriers.  Same-object
-- identification requires an explicit witness and is never inferred from a
-- matching label or date alone.
------------------------------------------------------------------------

data RecordingCarrierKind : Set where
  googleRecorderCapture : RecordingCarrierKind
  recordingsManifestRow : RecordingCarrierKind
  cloudRecordingCopy : RecordingCarrierKind
  downloadedComputerCopy : RecordingCarrierKind
  transcriptDerivative : RecordingCarrierKind
  archiveDerivative : RecordingCarrierKind
  submittedEvidenceDerivative : RecordingCarrierKind

record RecordingCarrier : Set₁ where
  constructor recordingCarrier
  field
    carrierKind : RecordingCarrierKind
    recordingReference : String
    storageReference : String
    timeReference : String
    carrierReceipt : Set

open RecordingCarrier public

record RecordingManifestIndex : Set₁ where
  constructor recordingManifestIndex
  field
    manifestReference : String
    manifestOwnerReference : String
    captureSystemReference : String
    indexReceipt : Set

open RecordingManifestIndex public

record ManifestRowIndexesRecording
    (manifest : RecordingManifestIndex)
    (row recording : RecordingCarrier) : Set₁ where
  constructor manifestRowIndexesRecording
  field
    rowIsManifestRow : carrierKind row ≡ recordingsManifestRow
    recordingIsCaptureOrCopy :
      (carrierKind recording ≡ googleRecorderCapture)
      ⊎
      (carrierKind recording ≡ cloudRecordingCopy)
      ⊎
      (carrierKind recording ≡ downloadedComputerCopy)
    rowReferenceMatchesRecordingReceipt : Set
    timestampOrFilenameMatchReceipt : Set
    indexRelationReference : String

open ManifestRowIndexesRecording public

------------------------------------------------------------------------
-- Same-object identity between storage/derivative carriers.
------------------------------------------------------------------------

record SameRecordingWitness
    (left right : RecordingCarrier) : Set₁ where
  constructor sameRecordingWitness
  field
    sameRecordingIdentityReceipt : Set
    filenameOrStableIdReceipt : Set
    temporalConsistencyReceipt : Set
    contentOrTranscriptConsistencyReceipt : Set
    sameObjectReference : String

open SameRecordingWitness public

record RecordingDerivationWitness
    (source derivative : RecordingCarrier) : Set₁ where
  constructor recordingDerivationWitness
  field
    derivativeProducedFromSourceReceipt : Set
    transformationReference : String
    identityPreservationReceipt : Set
    derivationReference : String

open RecordingDerivationWitness public

record SubmittedRecordingWitness
    (recording submitted : RecordingCarrier) : Set₁ where
  constructor submittedRecordingWitness
  field
    submittedIsEvidenceDerivative :
      carrierKind submitted ≡ submittedEvidenceDerivative
    sameRecording : SameRecordingWitness recording submitted
    submissionCarrierReference : String
    submissionReceipt : Set
    submissionReference : String

open SubmittedRecordingWitness public

------------------------------------------------------------------------
-- Storage movement is not recording identity loss.
------------------------------------------------------------------------

record QuotaDrivenCopyMigration
    (cloud local : RecordingCarrier) : Set₁ where
  constructor quotaDrivenCopyMigration
  field
    cloudIsCloudCopy : carrierKind cloud ≡ cloudRecordingCopy
    localIsDownloadedCopy : carrierKind local ≡ downloadedComputerCopy
    sameRecording : SameRecordingWitness cloud local
    migrationReasonReference : String
    migrationReceipt : Set

open QuotaDrivenCopyMigration public

------------------------------------------------------------------------
-- Source-scoped search support.  The manifest can be absent from one backup
-- while local copies/derivatives of indexed recordings are present there.
------------------------------------------------------------------------

record RecordingBackupTopology : Set₁ where
  constructor recordingBackupTopology
  field
    manifestPresentInBackup : Bool
    underlyingRecordingDerivativesPresentInBackup : Bool
    manifestAbsenceCancelsRecordingPresence : Bool
    manifestAbsenceCancelsRecordingPresenceIsFalse :
      manifestAbsenceCancelsRecordingPresence ≡ false
    topologyReference : String

open RecordingBackupTopology public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ManifestRowAutomaticallyRecording : Set where
data SameDateAutomaticallySameRecording : Set where
data SameFilenameAutomaticallySameRecording : Set where
data TranscriptAutomaticallyOriginalRecording : Set where
data BackupCopyAutomaticallySubmittedEvidence : Set where
data ManifestMissingAutomaticallyRecordingMissing : Set where
data StorageMigrationAutomaticallyBreaksIdentity : Set where

aManifestRowIsNotAutomaticallyRecording :
  ManifestRowAutomaticallyRecording → ⊥
aManifestRowIsNotAutomaticallyRecording ()

sameDateDoesNotIdentifyRecording :
  SameDateAutomaticallySameRecording → ⊥
sameDateDoesNotIdentifyRecording ()

sameFilenameDoesNotIdentifyRecording :
  SameFilenameAutomaticallySameRecording → ⊥
sameFilenameDoesNotIdentifyRecording ()

transcriptDoesNotAutomaticallyEqualOriginal :
  TranscriptAutomaticallyOriginalRecording → ⊥
transcriptDoesNotAutomaticallyEqualOriginal ()

backupCopyDoesNotAutomaticallyProveSubmission :
  BackupCopyAutomaticallySubmittedEvidence → ⊥
backupCopyDoesNotAutomaticallyProveSubmission ()

manifestMissingDoesNotMeanRecordingMissing :
  ManifestMissingAutomaticallyRecordingMissing → ⊥
manifestMissingDoesNotMeanRecordingMissing ()

storageMigrationDoesNotAutomaticallyBreakIdentity :
  StorageMigrationAutomaticallyBreaksIdentity → ⊥
storageMigrationDoesNotAutomaticallyBreakIdentity ()

------------------------------------------------------------------------
-- Canonical boundary.
------------------------------------------------------------------------

record RecordingManifestLineageBoundary : Set where
  constructor recordingManifestLineageBoundary
  field
    manifestRowEqualsRecording : Bool
    manifestRowEqualsRecordingIsFalse : manifestRowEqualsRecording ≡ false

    localCopyEqualsSubmission : Bool
    localCopyEqualsSubmissionIsFalse : localCopyEqualsSubmission ≡ false

    sameObjectWitnessRequiredAcrossCopies : Bool
    sameObjectWitnessRequiredAcrossCopiesIsTrue :
      sameObjectWitnessRequiredAcrossCopies ≡ true

    sameObjectWitnessRequiredForSubmittedDerivative : Bool
    sameObjectWitnessRequiredForSubmittedDerivativeIsTrue :
      sameObjectWitnessRequiredForSubmittedDerivative ≡ true

    manifestCanBeAbsentWhileRecordingDerivativePresent : Bool
    manifestCanBeAbsentWhileRecordingDerivativePresentIsTrue :
      manifestCanBeAbsentWhileRecordingDerivativePresent ≡ true

canonicalRecordingManifestLineageBoundary : RecordingManifestLineageBoundary
canonicalRecordingManifestLineageBoundary =
  recordingManifestLineageBoundary
    false refl
    false refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Russell / QCAT bounded fixture.
--
-- This pins only the carrier topology established by the current evidence:
-- the manifest indexes Google Recorder material; selected recordings were
-- downloaded to Dad's computer because of Drive quota; backup archives can
-- therefore survive without the manifest itself; the QCAT PDF independently
-- names selected recordings/transcripts.  It does not assert same-object
-- identity for any particular archive until a SameRecordingWitness is given.
------------------------------------------------------------------------

russellManifestReference : String
russellManifestReference = "Recordings and Transcriptions"

russellCaptureSystemReference : String
russellCaptureSystemReference = "Google Recorder"

russellDadAccountReference : String
russellDadAccountReference = "Dad Google account"

russellDadComputerReference : String
russellDadComputerReference = "Dad computer / TrueNAS-backed local copies"

russellQCATRecording26Jan : String
russellQCATRecording26Jan = "PXL_20220126_010646642.mp4 / Don't get too smart"

russellQCATInspection04Feb : String
russellQCATInspection04Feb = "2022-02-04 Inspection"

russellQCATInspection16Feb : String
russellQCATInspection16Feb = "2022-02-16 Inspection of breach"

record RussellRecordingLineageFixture : Set₁ where
  constructor russellRecordingLineageFixture
  field
    manifestReference : String
    manifestOwnerReference : String
    captureSystemReference : String
    downloadedCopyStorageReference : String
    qcatRecordingReferences : List String

    manifestIndexesRecorderCapturesReceipt : Set
    quotaDrivenDownloadsOccurredReceipt : Set
    backupContainsRecordingDerivativesReceipt : Set
    manifestNotFoundInBackupReceipt : Set

    sameObjectAcrossManifestAndBackupRequiresWitness : Bool
    sameObjectAcrossManifestAndBackupRequiresWitnessIsTrue :
      sameObjectAcrossManifestAndBackupRequiresWitness ≡ true

    sameObjectAcrossBackupAndQCATRequiresWitness : Bool
    sameObjectAcrossBackupAndQCATRequiresWitnessIsTrue :
      sameObjectAcrossBackupAndQCATRequiresWitness ≡ true

open RussellRecordingLineageFixture public

russellRecordingLineageFixture :
  (manifestReceipt : Set) →
  (quotaReceipt : Set) →
  (backupDerivativeReceipt : Set) →
  (manifestNonHitReceipt : Set) →
  RussellRecordingLineageFixture
russellRecordingLineageFixture
  manifestReceipt quotaReceipt backupDerivativeReceipt manifestNonHitReceipt =
  russellRecordingLineageFixture
    russellManifestReference
    russellDadAccountReference
    russellCaptureSystemReference
    russellDadComputerReference
    (russellQCATRecording26Jan ∷
     russellQCATInspection04Feb ∷
     russellQCATInspection16Feb ∷ [])
    manifestReceipt
    quotaReceipt
    backupDerivativeReceipt
    manifestNonHitReceipt
    true refl
    true refl
