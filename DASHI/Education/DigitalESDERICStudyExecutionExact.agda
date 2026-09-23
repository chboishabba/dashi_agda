module DASHI.Education.DigitalESDERICStudyExecutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDERICStudyInteropExact as ERIC
import DASHI.Education.DigitalESDTitleAbstractScreeningExact as Screen

------------------------------------------------------------------------
-- REAL ERIC CORPUS EXECUTION RECEIPT
--
-- Runtime owner:
--   interop_scripts/run_digital_esd_real_eric.py
--
-- This receipt is intentionally about execution of the real retained ERIC
-- export corpus through the parser/screening-worklist seam. It does not create
-- title/abstract decisions, full-text retrieval, source truth, or audit
-- admission.
------------------------------------------------------------------------

expectedRawQueryOccurrenceCount : Nat
expectedRawQueryOccurrenceCount = 46597

expectedUniqueERICRecordCount : Nat
expectedUniqueERICRecordCount = 43996

record RealERICStudyExecutionReceipt : Set where
  constructor real-eric-study-execution-receipt
  field
    wrapperVersion : String
    parserVersionReference : String
    exportRootReference : String

    observedRawQueryOccurrenceCount : Nat
    observedRawQueryOccurrenceCountIsExpected :
      observedRawQueryOccurrenceCount ≡ expectedRawQueryOccurrenceCount

    observedUniqueERICRecordCount : Nat
    observedUniqueERICRecordCountIsExpected :
      observedUniqueERICRecordCount ≡ expectedUniqueERICRecordCount

    parsedMetadataArtifactReference : String
    parsedMetadataArtifactSha256 : String
    parsedMetadataManifestReference : String
    parsedMetadataManifestSha256 : String

    unresolvedScreeningLedgerReference : String
    unresolvedScreeningLedgerSha256 : String
    screeningManifestReference : String
    screeningManifestSha256 : String

    candidateAssessmentReference : String
    candidateAssessmentSha256 : String
    studyFamilyHypothesisReference : String
    studyFamilyHypothesisSha256 : String
    studyFamilyFibreReference : String
    studyFamilyFibreSha256 : String

    calibrationSelectionReference : String
    calibrationSelectionSha256 : String
    calibrationEstimateReference : String
    calibrationEstimateSha256 : String
    paretoQueueReference : String
    paretoQueueSha256 : String
    paretoManifestReference : String
    paretoManifestSha256 : String

    parsesRealERICRatherThanSyntheticFixture : Bool
    parsesRealERICRatherThanSyntheticFixtureIsTrue :
      parsesRealERICRatherThanSyntheticFixture ≡ true

    stopsBeforeFullTextAcquisition : Bool
    stopsBeforeFullTextAcquisitionIsTrue :
      stopsBeforeFullTextAcquisition ≡ true

    createsScreeningDecision : Bool
    createsScreeningDecisionIsFalse :
      createsScreeningDecision ≡ false

    createsSourceTruth : Bool
    createsSourceTruthIsFalse :
      createsSourceTruth ≡ false

    createsSourceAuditAdmission : Bool
    createsSourceAuditAdmissionIsFalse :
      createsSourceAuditAdmission ≡ false

open RealERICStudyExecutionReceipt public

------------------------------------------------------------------------
-- Explicit composition with existing authorities.
------------------------------------------------------------------------

ericInteropAuthority : ERIC.ERICStudyInteropBoundary
ericInteropAuthority = ERIC.canonicalERICStudyInteropBoundary

screeningAuthority : Screen.ScreeningBoundary
screeningAuthority = Screen.canonicalScreeningBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RealERICWrapperCreatesScreeningDecision : Set where
data RealERICWrapperCreatesSourceTruth : Set where
data RealERICWrapperCreatesSourceAuditAdmission : Set where
data RealERICMetadataCorpusCountsAsFullTextCorpus : Set where
data SyntheticFixturePaysRealERICExecution : Set where
data QueryOverlapCreatesSameEmpiricalStudy : Set where
data ParsedAbstractCreatesCanonicalFullTextEvidence : Set where
data CandidateAssessmentCreatesReviewedDecision : Set where
data ParetoQueueCreatesReviewedDecision : Set where

realERICWrapperDoesNotCreateScreeningDecision :
  RealERICWrapperCreatesScreeningDecision → ⊥
realERICWrapperDoesNotCreateScreeningDecision ()

realERICWrapperDoesNotCreateSourceTruth :
  RealERICWrapperCreatesSourceTruth → ⊥
realERICWrapperDoesNotCreateSourceTruth ()

realERICWrapperDoesNotCreateSourceAuditAdmission :
  RealERICWrapperCreatesSourceAuditAdmission → ⊥
realERICWrapperDoesNotCreateSourceAuditAdmission ()

realERICMetadataCorpusDoesNotCountAsFullTextCorpus :
  RealERICMetadataCorpusCountsAsFullTextCorpus → ⊥
realERICMetadataCorpusDoesNotCountAsFullTextCorpus ()

syntheticFixtureDoesNotPayRealERICExecution :
  SyntheticFixturePaysRealERICExecution → ⊥
syntheticFixtureDoesNotPayRealERICExecution ()

queryOverlapDoesNotCreateSameEmpiricalStudy :
  QueryOverlapCreatesSameEmpiricalStudy → ⊥
queryOverlapDoesNotCreateSameEmpiricalStudy ()

parsedAbstractDoesNotCreateCanonicalFullTextEvidence :
  ParsedAbstractCreatesCanonicalFullTextEvidence → ⊥
parsedAbstractDoesNotCreateCanonicalFullTextEvidence ()

candidateAssessmentDoesNotCreateReviewedDecision :
  CandidateAssessmentCreatesReviewedDecision → ⊥
candidateAssessmentDoesNotCreateReviewedDecision ()

paretoQueueDoesNotCreateReviewedDecision :
  ParetoQueueCreatesReviewedDecision → ⊥
paretoQueueDoesNotCreateReviewedDecision ()

------------------------------------------------------------------------
-- Execution boundary.
------------------------------------------------------------------------

record RealERICExecutionBoundary : Set where
  constructor real-eric-execution-boundary
  field
    exactExpectedOccurrenceCountPinned : Bool
    exactExpectedOccurrenceCountPinnedIsTrue :
      exactExpectedOccurrenceCountPinned ≡ true

    exactExpectedUniqueCountPinned : Bool
    exactExpectedUniqueCountPinnedIsTrue :
      exactExpectedUniqueCountPinned ≡ true

    everyOutputArtifactHasDigest : Bool
    everyOutputArtifactHasDigestIsTrue :
      everyOutputArtifactHasDigest ≡ true

    parserAndLedgerRemainDistinct : Bool
    parserAndLedgerRemainDistinctIsTrue :
      parserAndLedgerRemainDistinct ≡ true

    metadataAndFullTextRemainDistinct : Bool
    metadataAndFullTextRemainDistinctIsTrue :
      metadataAndFullTextRemainDistinct ≡ true

    runtimeReceiptMayPayOnlyObservedRun : Bool
    runtimeReceiptMayPayOnlyObservedRunIsTrue :
      runtimeReceiptMayPayOnlyObservedRun ≡ true

    syntheticFixtureMayPayRealRun : Bool
    syntheticFixtureMayPayRealRunIsFalse :
      syntheticFixtureMayPayRealRun ≡ false

open RealERICExecutionBoundary public

canonicalRealERICExecutionBoundary : RealERICExecutionBoundary
canonicalRealERICExecutionBoundary =
  real-eric-execution-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl

realERICExecutionReading : String
realERICExecutionReading =
  "The Digital-ESD real-ERIC execution receipt binds one observed run of the retained Q1-Q7 ERIC exports to exactly 46,597 raw query occurrences and 43,996 stable unique ERIC metadata/abstract records, plus SHA-256 references for the parser output, unresolved screening ledger, candidate assessments, study-family hypotheses/fibres, calibration artifacts and Pareto work queue. This is a real metadata-screening execution receipt only. Abstract parsing is not full-text parsing; query overlap is not same-study identity; candidate assessment/Pareto output is not a reviewed screening decision; and the wrapper creates neither source truth nor SourceAuditAdmission."
