module DASHI.Law.SensibLawBackupNegativeEvidenceBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawTemporalHealthEvidenceWrongTypeExact as TemporalHealth

------------------------------------------------------------------------
-- SOURCE-SCOPED BACKUP NEGATIVE EVIDENCE
--
-- DASHI-original epistemic/provenance boundary.
--
-- A read-only backup search can independently corroborate carriers that are
-- present in that backup.  Failure to find another carrier in the searched
-- backup is source-scoped negative evidence only.  It cannot silently become
-- a proof that the carrier never existed, was never stored elsewhere, or was
-- never submitted through another route.
------------------------------------------------------------------------

data BackupSearchOutcome : Set where
  carrierFoundInBackup : BackupSearchOutcome
  carrierNotFoundInBackup : BackupSearchOutcome
  backupSearchIncomplete : BackupSearchOutcome
  backupSearchOutcomeUnresolved : BackupSearchOutcome


data CrossSourceSupport : Set where
  independentlyCorroborated : CrossSourceSupport
  sourceDependent : CrossSourceSupport
  contradictedByIndependentSource : CrossSourceSupport
  crossSourceSupportUnresolved : CrossSourceSupport


record BackupSearchScope : Set₁ where
  constructor backupSearchScope
  field
    backupRootReference : String
    searchModeReference : String
    searchedCarrierClasses : List String
    readOnlyReceipt : Set
    scopeReference : String

open BackupSearchScope public

record BackupCarrierFinding (scope : BackupSearchScope) : Set₁ where
  constructor backupCarrierFinding
  field
    carrierReference : String
    outcome : BackupSearchOutcome
    findingReceipt : Set
    findingReference : String

open BackupCarrierFinding public

------------------------------------------------------------------------
-- Same-object corroboration across duplicate backup copies.
------------------------------------------------------------------------

record HashIdentityCorroboration : Set₁ where
  constructor hashIdentityCorroboration
  field
    firstCarrierReference : String
    secondCarrierReference : String
    digestAlgorithmReference : String
    firstDigestReference : String
    secondDigestReference : String
    sameDigestReceipt : Set
    corroborationReference : String

open HashIdentityCorroboration public

------------------------------------------------------------------------
-- Backup support for a temporal-health evidence claim.
------------------------------------------------------------------------

record TemporalHealthBackupSupport : Set₁ where
  constructor temporalHealthBackupSupport
  field
    finalBundleFinding : BackupSearchOutcome
    supportingArchiveFindings : List String
    laterMedicalCarrierFindings : List String

    recordingsSpreadsheetFinding : BackupSearchOutcome
    separateBloodPressureCarrierFinding : BackupSearchOutcome

    finalBundleSupport : CrossSourceSupport
    specificBloodPressureEntrySupport : CrossSourceSupport
    separateSpreadsheetSubmissionSupport : CrossSourceSupport

    supportReference : String

open TemporalHealthBackupSupport public

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record BackupNegativeEvidenceBoundary : Set where
  constructor backupNegativeEvidenceBoundary
  field
    notFoundInBackupMeansNeverExisted : Bool
    notFoundInBackupMeansNeverExistedIsFalse :
      notFoundInBackupMeansNeverExisted ≡ false

    notFoundInBackupMeansNeverSubmitted : Bool
    notFoundInBackupMeansNeverSubmittedIsFalse :
      notFoundInBackupMeansNeverSubmitted ≡ false

    foundFinalBundleConfirmsEmbeddedPages : Bool
    foundFinalBundleConfirmsEmbeddedPagesIsTrue :
      foundFinalBundleConfirmsEmbeddedPages ≡ true

    missingSeparateCarrierCancelsEmbeddedEvidence : Bool
    missingSeparateCarrierCancelsEmbeddedEvidenceIsFalse :
      missingSeparateCarrierCancelsEmbeddedEvidence ≡ false

    crossSourceSupportMustRemainClaimSpecific : Bool
    crossSourceSupportMustRemainClaimSpecificIsTrue :
      crossSourceSupportMustRemainClaimSpecific ≡ true

canonicalBackupNegativeEvidenceBoundary : BackupNegativeEvidenceBoundary
canonicalBackupNegativeEvidenceBoundary =
  backupNegativeEvidenceBoundary
    false refl
    false refl
    true refl
    false refl
    true refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data BackupNonHitAutomaticallyNonExistence : Set where
data BackupNonHitAutomaticallyNonSubmission : Set where
data MissingSpreadsheetAutomaticallyNegatesEmbeddedCharts : Set where
data FinalBundlePresenceAutomaticallyConfirmsSpecificExternalSpreadsheetRow : Set where

backupNonHitDoesNotProveNonExistence :
  BackupNonHitAutomaticallyNonExistence → ⊥
backupNonHitDoesNotProveNonExistence ()

backupNonHitDoesNotProveNonSubmission :
  BackupNonHitAutomaticallyNonSubmission → ⊥
backupNonHitDoesNotProveNonSubmission ()

missingSpreadsheetDoesNotNegateEmbeddedCharts :
  MissingSpreadsheetAutomaticallyNegatesEmbeddedCharts → ⊥
missingSpreadsheetDoesNotNegateEmbeddedCharts ()

finalBundleDoesNotAutoConfirmExternalSpreadsheetRow :
  FinalBundlePresenceAutomaticallyConfirmsSpecificExternalSpreadsheetRow → ⊥
finalBundleDoesNotAutoConfirmExternalSpreadsheetRow ()

------------------------------------------------------------------------
-- Russell / QCAT 0096/22 bounded regression.
--
-- This fixture encodes only the corrected source-support topology:
--
-- * the TrueNAS backup independently contains the final annotated QCAT bundle
--   and related Russell/QCAT recording/archive material;
-- * the final QCAT carrier contains the embedded health tables/charts already
--   represented by TemporalHealth.qcat0096HealthPages;
-- * the searched backup did not yield the separate Recordings and
--   Transcriptions spreadsheet or a standalone blood-pressure carrier;
-- * therefore the specific 14-Feb spreadsheet row remains source-dependent on
--   the separately recovered spreadsheet carrier;
-- * absence from this backup does not prove that such a carrier did not exist
--   elsewhere or was not submitted by another route.
------------------------------------------------------------------------

russellBackupRoot : String
russellBackupRoot = "/mnt/truenas/gem-net/One Touch - Backup/Johl/"

russellFinalBundleBackupReference : String
russellFinalBundleBackupReference =
  "Documents/_FINAL ANNOTATED Russell Minor Civil Dispute QCAT 43pg 13-05-22.docx"

russellPixel6BundleBackupReference : String
russellPixel6BundleBackupReference =
  "pixel6/Documents/Caton v Brown/_FINAL ANNOTATED Russell Minor Civil Dispute QCAT 43pg 13-05-22.docx"

russellInspectionArchiveReference : String
russellInspectionArchiveReference = "Inspection.zip"

russellInspectionOfBreachArchiveReference : String
russellInspectionOfBreachArchiveReference = "Inspection of breach.zip"

russellInjuriesArchiveReference : String
russellInjuriesArchiveReference =
  "Transcribe both ends, inspection of breach last, conversation about innuries first .zip"

russellDontGetTooSmartArchiveReference : String
russellDontGetTooSmartArchiveReference = "Transcript Dont get too smart.zip"

russellLaterMedicalReportReference : String
russellLaterMedicalReportReference = "30.6.2022. J. Brown Med Report.pdf"

record RussellBackupCorrectionFixture : Set₁ where
  constructor russellBackupCorrectionFixture
  field
    backupRootReference : String
    finalBundleReference : String
    duplicateBundleReference : String
    relatedArchiveReferences : List String
    laterMedicalReference : String

    duplicateBundleSameHashReceipt : Set
    finalBundlePresentReceipt : Set
    relatedArchivesPresentReceipt : Set

    recordingsAndTranscriptionsNotFoundInSearchedBackup : Set
    standaloneBloodPressureCarrierNotFoundInSearchedBackup : Set

    finalBundleIndependentlyCorroborated : CrossSourceSupport
    specific14FebSpreadsheetEntryIndependentlyCorroborated : CrossSourceSupport
    separateSpreadsheetSubmissionIndependentlyCorroborated : CrossSourceSupport

    embeddedHealthPagesReference : String
    embeddedHealthPagesRemainConfirmed : Bool
    embeddedHealthPagesRemainConfirmedIsTrue :
      embeddedHealthPagesRemainConfirmed ≡ true

open RussellBackupCorrectionFixture public

russellBackupCorrectionFixture :
  (sameHashReceipt : Set) →
  (bundleReceipt : Set) →
  (archivesReceipt : Set) →
  (spreadsheetNonHitReceipt : Set) →
  (bpCarrierNonHitReceipt : Set) →
  RussellBackupCorrectionFixture
russellBackupCorrectionFixture
  sameHashReceipt
  bundleReceipt
  archivesReceipt
  spreadsheetNonHitReceipt
  bpCarrierNonHitReceipt =
  russellBackupCorrectionFixture
    russellBackupRoot
    russellFinalBundleBackupReference
    russellPixel6BundleBackupReference
    (russellInspectionArchiveReference ∷
     russellInspectionOfBreachArchiveReference ∷
     russellInjuriesArchiveReference ∷
     russellDontGetTooSmartArchiveReference ∷ [])
    russellLaterMedicalReportReference
    sameHashReceipt
    bundleReceipt
    archivesReceipt
    spreadsheetNonHitReceipt
    bpCarrierNonHitReceipt
    independentlyCorroborated
    sourceDependent
    sourceDependent
    TemporalHealth.qcat0096HealthPages
    true refl
