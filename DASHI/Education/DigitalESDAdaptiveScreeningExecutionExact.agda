module DASHI.Education.DigitalESDAdaptiveScreeningExecutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDAdaptiveScreeningControllerExact as Controller
import DASHI.Education.DigitalESDTitleAbstractScreeningExact as Screening
import DASHI.Education.DigitalESDSLRSourceReviewBridgeExact as SLR
import DASHI.Education.DigitalESDSourceAuditAdmissionExact as Audit

------------------------------------------------------------------------
-- DIGITAL-ESD P0-A -> P0-G EXECUTION PARITY
--
-- Runtime owner:
--   scripts/run_digital_esd_adaptive_screening.py
--
-- This owner records the executable realization of the already-paid controller
-- semantics. Runtime outputs remain work-selection / candidate artifacts.
-- Only explicit screening review can change ScreeningDecisionReceipt.
------------------------------------------------------------------------

record P0AExactUniverseExecutionParity : Set where
  constructor p0a-exact-universe-execution-parity
  field
    consumesDurableScreeningLedger : Bool
    retainsLedgerSha256 : Bool
    emitsDenominatorIntegrityReceipt : Bool
    n0EqualsReviewedPlusStillUnreviewed : Bool
    unresolvedRemainsDistinctFromExclude : Bool

open P0AExactUniverseExecutionParity public

canonicalP0AExecution : P0AExactUniverseExecutionParity
canonicalP0AExecution =
  p0a-exact-universe-execution-parity true true true true true

record P0BCandidateAssessmentExecutionParity : Set where
  constructor p0b-candidate-assessment-execution-parity
  field
    oneCandidateAssessmentPerLedgerRow : Bool
    exactMetadataRevisionRetained : Bool
    exactTitleAbstractSnapshotRetained : Bool
    modelReferenceExplicit : Bool
    featureEvidenceExplicit : Bool
    candidateAssessmentCreatesScreeningDecision : Bool
    candidateAssessmentCreatesSourceTruth : Bool

open P0BCandidateAssessmentExecutionParity public

canonicalP0BExecution : P0BCandidateAssessmentExecutionParity
canonicalP0BExecution =
  p0b-candidate-assessment-execution-parity
    true true true true true false false

record P0CStudyFamilyExecutionParity : Set where
  constructor p0c-study-family-execution-parity
  field
    candidateFibresEmitted : Bool
    relationKindExplicit : Bool
    evidenceReferenceExplicit : Bool
    candidateFibreCreatesSameEmpiricalStudyIdentity : Bool

open P0CStudyFamilyExecutionParity public

canonicalP0CExecution : P0CStudyFamilyExecutionParity
canonicalP0CExecution =
  p0c-study-family-execution-parity true true true false

record P0DCalibrationExecutionParity : Set where
  constructor p0d-calibration-execution-parity
  field
    obviousRetainedStratumSupported : Bool
    obviousExclusionStratumSupported : Bool
    highUncertaintyStratumSupported : Bool
    duplicateAmbiguityStratumSupported : Bool
    rareTerminologyOrSourceTypeStratumSupported : Bool
    missingAbstractOrMalformedMetadataStratumSupported : Bool
    selectionCreatesScreeningDecision : Bool

open P0DCalibrationExecutionParity public

canonicalP0DExecution : P0DCalibrationExecutionParity
canonicalP0DExecution =
  p0d-calibration-execution-parity
    true true true true true true false

record P0ECalibrationDiagnosticsExecutionParity : Set where
  constructor p0e-calibration-diagnostics-execution-parity
  field
    reviewedDecisionSurfaceOnly : Bool
    falseNegativeRiskReferenceEmitted : Bool
    disagreementStructureEmitted : Bool
    rubricAmbiguityReferenceEmitted : Bool
    residualClassesEmitted : Bool
    diagnosticsCreateAutomaticDecisionAuthority : Bool

open P0ECalibrationDiagnosticsExecutionParity public

canonicalP0EExecution : P0ECalibrationDiagnosticsExecutionParity
canonicalP0EExecution =
  p0e-calibration-diagnostics-execution-parity
    true true true true true false

record P0FParetoExecutionParity : Set where
  constructor p0f-pareto-execution-parity
  field
    boundaryInformationGainRetained : Bool
    likelyCorpusContractionRetained : Bool
    rareCellCoverageRetained : Bool
    duplicateFamilyPayoffRetained : Bool
    reviewerCostRetained : Bool
    paretoFrontExplicit : Bool
    unselectedRemainInDenominator : Bool
    selectorCreatesScreeningDecision : Bool

open P0FParetoExecutionParity public

canonicalP0FExecution : P0FParetoExecutionParity
canonicalP0FExecution =
  p0f-pareto-execution-parity
    true true true true true true true false

record P0GFullTextExecutionParity : Set where
  constructor p0g-fulltext-execution-parity
  field
    includeOrProbableRequired : Bool
    fullTextArtifactIdentityRequired : Bool
    fullTextSha256Required : Bool
    fullTextDigestComputedFromArtifact : Bool
    fullTextUnavailableAttemptRetained : Bool
    sameObjectIdentityReviewRequired : Bool
    slrSourceUnitManifestEmitted : Bool
    canonicalSLREvidenceRequired : Bool
    reviewedSLREvidenceRequired : Bool
    digitalESDAuditProjectionRequired : Bool
    sourceAuditAdmissionStillRequired : Bool
    corpusAuditedSourceStillRequired : Bool
    hyperfabricAuditRequired : Bool
    frameworkChallengeRequired : Bool
    screeningCreatesAuditAdmission : Bool
    slrCreatesAuditAdmission : Bool

open P0GFullTextExecutionParity public

canonicalP0GExecution : P0GFullTextExecutionParity
canonicalP0GExecution =
  p0g-fulltext-execution-parity
    true true true true true true true true true true true true true true
    false false

record P0AToGExecutionBoundary : Set where
  constructor p0-a-to-g-execution-boundary
  field
    p0AImplemented : Bool
    p0BImplemented : Bool
    p0CImplemented : Bool
    p0DImplemented : Bool
    p0EImplemented : Bool
    p0FImplemented : Bool
    p0GImplemented : Bool
    exact43996ExecutionObserved : Bool
    explicitScreeningReviewObserved : Bool
    fullTextRetrievalObserved : Bool

open P0AToGExecutionBoundary public

currentP0AToGExecutionBoundary : P0AToGExecutionBoundary
currentP0AToGExecutionBoundary =
  p0-a-to-g-execution-boundary
    true true true true true true true
    false false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RuntimeCandidateAssessmentCreatesScreeningDecision : Set where
data RuntimeParetoSelectionCreatesScreeningDecision : Set where
data RuntimeUnselectedRecordLeavesDenominator : Set where
data RuntimeFamilyHypothesisCreatesEmpiricalStudyIdentity : Set where
data RuntimeMissingAbstractCreatesExclusion : Set where
data RuntimeScreeningCreatesAuditAdmission : Set where
data RuntimeSLRHandoffCreatesAuditAdmission : Set where

runtimeCandidateAssessmentCannotCreateScreeningDecision :
  RuntimeCandidateAssessmentCreatesScreeningDecision → ⊥
runtimeCandidateAssessmentCannotCreateScreeningDecision ()

runtimeParetoSelectionCannotCreateScreeningDecision :
  RuntimeParetoSelectionCreatesScreeningDecision → ⊥
runtimeParetoSelectionCannotCreateScreeningDecision ()

runtimeUnselectedRecordCannotLeaveDenominator :
  RuntimeUnselectedRecordLeavesDenominator → ⊥
runtimeUnselectedRecordCannotLeaveDenominator ()

runtimeFamilyHypothesisCannotCreateEmpiricalStudyIdentity :
  RuntimeFamilyHypothesisCreatesEmpiricalStudyIdentity → ⊥
runtimeFamilyHypothesisCannotCreateEmpiricalStudyIdentity ()

runtimeMissingAbstractCannotCreateExclusion :
  RuntimeMissingAbstractCreatesExclusion → ⊥
runtimeMissingAbstractCannotCreateExclusion ()

runtimeScreeningCannotCreateAuditAdmission :
  RuntimeScreeningCreatesAuditAdmission → ⊥
runtimeScreeningCannotCreateAuditAdmission ()

runtimeSLRHandoffCannotCreateAuditAdmission :
  RuntimeSLRHandoffCreatesAuditAdmission → ⊥
runtimeSLRHandoffCannotCreateAuditAdmission ()

controllerBoundaryAnchor : Controller.P0ExecutionBoundary
controllerBoundaryAnchor = Controller.canonicalP0ExecutionBoundary

screeningBoundaryAnchor : Screening.ScreeningBoundary
screeningBoundaryAnchor = Screening.canonicalScreeningBoundary

sourceAuditBoundaryAnchor : Audit.SourceAuditAdmissionBoundary
sourceAuditBoundaryAnchor = Audit.canonicalSourceAuditAdmissionBoundary
