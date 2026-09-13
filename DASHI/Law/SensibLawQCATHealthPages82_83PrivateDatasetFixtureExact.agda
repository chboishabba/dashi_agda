module DASHI.Law.SensibLawQCATHealthPages82_83PrivateDatasetFixtureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.SourceConditionedObservationExact as Observation
import DASHI.Law.SensibLawHealthRecordEvidenceExact as Health

------------------------------------------------------------------------
-- PRIVACY-PRESERVING QCAT PP.82-83 TRANSCRIPTION FIXTURE
--
-- The raw physiological values and personal notes are intentionally NOT
-- committed to this public repository.  The complete manual transcription is
-- held as a private workbook and is referenced here by a canonical digest plus
-- row/schema receipts.  This lets downstream code test the generic ingestion
-- contract without republishing personal health measurements.
------------------------------------------------------------------------

qcatHealthCarrierReference : String
qcatHealthCarrierReference =
  "QCAT 0096/22 final 83-page submitted carrier, physiological tables/charts pp.82-83"

privateTranscriptionDigestSha256 : String
privateTranscriptionDigestSha256 =
  "094054ed14017fd8552c3f81c80a6e4d65e10944ade0a9b901186a6855b34d60"

privateTranscriptionArtifactReference : String
privateTranscriptionArtifactReference =
  "qcat_health_pp82_83_transcription.xlsx"

record PrivateHistoricalHealthDatasetReceipt : Set₁ where
  constructor privateHistoricalHealthDatasetReceipt
  field
    sourceCarrierReference : String
    privateArtifactReference : String
    canonicalDigestReference : String
    subjectOneReference : String
    subjectOneRowCountReference : String
    subjectTwoReference : String
    subjectTwoRowCountReference : String
    combinedRowCountReference : String
    schemaReference : String
    rawDatesPreservedReceipt : Set
    sourceTyposNotSilentlyRewrittenReceipt : Set
    literalFailureCellsPreservedReceipt : Set
    partialNotesExplicitReceipt : Set

open PrivateHistoricalHealthDatasetReceipt public

qcatPages82_83PrivateDataset :
  (rawDatesPreservedReceipt : Set) →
  (sourceTyposNotSilentlyRewrittenReceipt : Set) →
  (literalFailureCellsPreservedReceipt : Set) →
  (partialNotesExplicitReceipt : Set) →
  PrivateHistoricalHealthDatasetReceipt
qcatPages82_83PrivateDataset
  rawDatesPreservedReceipt
  sourceTyposNotSilentlyRewrittenReceipt
  literalFailureCellsPreservedReceipt
  partialNotesExplicitReceipt =
  privateHistoricalHealthDatasetReceipt
    qcatHealthCarrierReference
    privateTranscriptionArtifactReference
    privateTranscriptionDigestSha256
    "Johl"
    "38 source rows"
    "John"
    "51 source rows"
    "89 combined source rows"
    "date_raw,time_raw,sleep,tobacco,coffee,thc,o2,o2_bpm,systolic,diastolic,bp_bpm,note,status"
    rawDatesPreservedReceipt
    sourceTyposNotSilentlyRewrittenReceipt
    literalFailureCellsPreservedReceipt
    partialNotesExplicitReceipt

------------------------------------------------------------------------
-- Generic carrier adapters.  These do not expose the private values.
------------------------------------------------------------------------

qcatPages82_83SourceArtifact : Observation.SourceArtifact
qcatPages82_83SourceArtifact =
  Observation.sourceArtifact
    "qcat-0096-22-health-pp82-83"
    Observation.measurementArtifact
    qcatHealthCarrierReference
    "QCAT submitted evidence carrier"

qcatPages82_83HealthArtifact :
  (provenanceReceipt : Set) → Health.HealthRecordArtifact
qcatPages82_83HealthArtifact provenanceReceipt =
  Health.healthRecordArtifact
    qcatPages82_83SourceArtifact
    Health.physiologicalTable
    "two-subject historical health table"
    "source-authored table embedded in submitted QCAT carrier"
    "23 February 2022 through 3 March 2022 source window"
    "historical physiological observation window"
    (Observation.provenanceAnchor
      "embedded pages 82-83 provenance"
      "source rows carry raw date/time strings"
      privateTranscriptionDigestSha256
      provenanceReceipt)

record PrivateDatasetIngestionBoundary : Set where
  constructor privateDatasetIngestionBoundary
  field
    publicRepoContainsRawMeasurements : Bool
    publicRepoContainsRawMeasurementsIsFalse :
      publicRepoContainsRawMeasurements ≡ false

    digestAloneEstablishesObservationTruth : Bool
    digestAloneEstablishesObservationTruthIsFalse :
      digestAloneEstablishesObservationTruth ≡ false

    rawTimeSeriesAutomaticallyDiagnosis : Bool
    rawTimeSeriesAutomaticallyDiagnosisIsFalse :
      rawTimeSeriesAutomaticallyDiagnosis ≡ false

    rawTimeSeriesAutomaticallyCausation : Bool
    rawTimeSeriesAutomaticallyCausationIsFalse :
      rawTimeSeriesAutomaticallyCausation ≡ false

canonicalPrivateDatasetIngestionBoundary : PrivateDatasetIngestionBoundary
canonicalPrivateDatasetIngestionBoundary =
  privateDatasetIngestionBoundary
    false refl
    false refl
    false refl
    false refl
