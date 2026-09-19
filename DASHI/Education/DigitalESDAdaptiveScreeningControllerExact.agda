module DASHI.Education.DigitalESDAdaptiveScreeningControllerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto
import DASHI.Education.DigitalESDTitleAbstractScreeningExact as Screen
import DASHI.Education.DigitalESDSearchToSourceAuditAdmissionExact as Audit
import DASHI.Education.DigitalESDSLRSourceReviewBridgeExact as SLR
import DASHI.Education.DigitalESDSituatedAuditObserverExact as Situated
import DASHI.Education.DigitalESDEligibilityFrameExclusionExact as Frame

------------------------------------------------------------------------
-- DIGITAL-ESD P0-A -> P0-G ADAPTIVE SCREENING CONTROLLER
--
-- The computational layer may observe, cluster and prioritise the exact
-- screening universe. It cannot silently turn a candidate assessment, score,
-- cluster or selection decision into title/abstract inclusion or exclusion.
------------------------------------------------------------------------

data CalibrationStratum : Set where
  obviousRetainedCandidate
  obviousExclusionCandidate
  highUncertainty
  duplicateAmbiguity
  rareTerminologyOrSourceType
  missingAbstractOrMalformedMetadata
  : CalibrationStratum

data ScreeningPriorityAxis : Set where
  boundaryInformationGain
  likelyCorpusContraction
  rareCellCoverage
  duplicateFamilyPayoff
  reviewerCost
  : ScreeningPriorityAxis

record ScreeningCandidateAssessment : Set where
  constructor screening-candidate-assessment
  field
    sourceIdentityReference : String
    metadataRevisionReference : String
    titleAbstractSnapshotReference : String
    rubricVersion : String
    candidateDecision : Screen.ScreeningDecision
    confidenceReference : String
    marginReference : String
    reasonCodeCandidatesReference : String
    modelReference : String
    featureEvidenceReference : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsScreeningDecision : Bool
    createsScreeningDecisionIsFalse : createsScreeningDecision ≡ false
    createsSourceTruth : Bool
    createsSourceTruthIsFalse : createsSourceTruth ≡ false

open ScreeningCandidateAssessment public

record StudyFamilyHypothesis : Set where
  constructor study-family-hypothesis
  field
    fibreReference : String
    memberSourceReferences : List String
    relationKind : Screen.DuplicateRelationKind
    evidenceReference : String
    reviewedAsSameObject : Bool
    hypothesisCreatesEmpiricalStudyIdentity : Bool
    hypothesisCreatesEmpiricalStudyIdentityIsFalse :
      hypothesisCreatesEmpiricalStudyIdentity ≡ false

open StudyFamilyHypothesis public

record ScreeningDenominatorIntegrityReceipt : Set where
  constructor screening-denominator-integrity-receipt
  field
    exactUniverseReference : String
    exactUniverseSha256 : String
    n0Reference : String
    reviewedReference : String
    stillUnreviewedReference : String
    includeReference : String
    probableReference : String
    excludeReference : String
    unresolvedReference : String
    reportFamilyReference : String
    fullTextSoughtReference : String
    fullTextObtainedReference : String
    fullTextUnavailableReference : String
    auditAdmittedReference : String
    rejectedAfterFullTextReference : String
    n0PartitionedByReviewedPlusUnreviewed : Bool
    n0PartitionedByReviewedPlusUnreviewedIsTrue :
      n0PartitionedByReviewedPlusUnreviewed ≡ true
    everyUniverseMemberRetained : Bool
    everyUniverseMemberRetainedIsTrue : everyUniverseMemberRetained ≡ true
    unresolvedIsNotExclusion : Bool
    unresolvedIsNotExclusionIsTrue : unresolvedIsNotExclusion ≡ true

open ScreeningDenominatorIntegrityReceipt public

record AdaptiveSelectionReceipt : Set where
  constructor adaptive-selection-receipt
  field
    unresolvedUniverseReference : String
    calibrationRoundReference : String
    selectedSourceReferences : List String
    paretoFrontReference : String
    informationGainReference : String
    contractionReference : String
    rareCellCoverageReference : String
    duplicatePayoffReference : String
    reviewerCostReference : String
    selectionCreatesScreeningDecision : Bool
    selectionCreatesScreeningDecisionIsFalse :
      selectionCreatesScreeningDecision ≡ false
    prioritisationMayDropUnselectedFromLedger : Bool
    prioritisationMayDropUnselectedFromLedgerIsFalse :
      prioritisationMayDropUnselectedFromLedger ≡ false

open AdaptiveSelectionReceipt public

record CalibrationReceipt : Set where
  constructor calibration-receipt
  field
    calibrationRoundReference : String
    strataReference : String
    reviewedDecisionReference : String
    falseNegativeRiskReference : String
    disagreementStructureReference : String
    rubricAmbiguityReference : String
    residualClassReference : String
    calibrationCreatesAutomaticDecisionAuthority : Bool
    calibrationCreatesAutomaticDecisionAuthorityIsFalse :
      calibrationCreatesAutomaticDecisionAuthority ≡ false

open CalibrationReceipt public

record P0GFullTextHandoffReceipt : Set where
  constructor p0g-fulltext-handoff-receipt
  field
    retainedScreeningDecisionReference : String
    retainedDecisionIsIncludeOrProbable : Bool
    retainedDecisionIsIncludeOrProbableIsTrue :
      retainedDecisionIsIncludeOrProbable ≡ true
    fullTextAcquisitionReference : String
    fullTextIdentityReviewReference : String
    canonicalSLREvidenceReference : String
    reviewedSLREvidenceReference : String
    digitalESDAuditProjectionReference : String
    sourceAuditAdmissionReference : String
    corpusAuditedSourceReference : String
    hyperfabricAuditReference : String
    frameworkChallengeReference : String
    screeningAloneCreatesAuditAdmission : Bool
    screeningAloneCreatesAuditAdmissionIsFalse :
      screeningAloneCreatesAuditAdmission ≡ false
    slrAloneCreatesAuditAdmission : Bool
    slrAloneCreatesAuditAdmissionIsFalse :
      slrAloneCreatesAuditAdmission ≡ false

open P0GFullTextHandoffReceipt public

record P0ExecutionBoundary : Set where
  constructor p0-execution-boundary
  field
    p0AExactUnresolvedLedger : Bool
    p0BCandidateAssessmentNonAuthoritative : Bool
    p0CCandidateStudyFibresNonAuthoritative : Bool
    p0DStratifiedCalibration : Bool
    p0EReviewedCalibrationDiagnostics : Bool
    p0FParetoAdaptiveSelection : Bool
    p0GFullTextCanonicalReviewAuditRoute : Bool
    modelMayExcludeWithoutReview : Bool
    modelMayExcludeWithoutReviewIsFalse : modelMayExcludeWithoutReview ≡ false
    selectorMayExcludeWithoutReview : Bool
    selectorMayExcludeWithoutReviewIsFalse : selectorMayExcludeWithoutReview ≡ false
    duplicateHypothesisMayCreateStudyIdentity : Bool
    duplicateHypothesisMayCreateStudyIdentityIsFalse :
      duplicateHypothesisMayCreateStudyIdentity ≡ false
    screeningAndFullTextAuditCollapsed : Bool
    screeningAndFullTextAuditCollapsedIsFalse :
      screeningAndFullTextAuditCollapsed ≡ false

open P0ExecutionBoundary public

canonicalP0ExecutionBoundary : P0ExecutionBoundary
canonicalP0ExecutionBoundary =
  p0-execution-boundary
    true true true true true true true
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CandidateAssessmentCreatesScreeningDecision : Set where
data CandidateAssessmentCreatesSourceTruth : Set where
data SelectorCreatesScreeningDecision : Set where
data UnselectedRecordMayLeaveDenominator : Set where
data FibreHypothesisCreatesStudyIdentity : Set where
data MissingAbstractMeansExclude : Set where
data ScreeningDecisionCreatesAuditAdmission : Set where
data SLRReviewCreatesAuditAdmission : Set where

candidateAssessmentCannotCreateScreeningDecision :
  CandidateAssessmentCreatesScreeningDecision → ⊥
candidateAssessmentCannotCreateScreeningDecision ()

candidateAssessmentCannotCreateSourceTruth :
  CandidateAssessmentCreatesSourceTruth → ⊥
candidateAssessmentCannotCreateSourceTruth ()

selectorCannotCreateScreeningDecision :
  SelectorCreatesScreeningDecision → ⊥
selectorCannotCreateScreeningDecision ()

unselectedRecordCannotLeaveDenominator :
  UnselectedRecordMayLeaveDenominator → ⊥
unselectedRecordCannotLeaveDenominator ()

fibreHypothesisCannotCreateStudyIdentity :
  FibreHypothesisCreatesStudyIdentity → ⊥
fibreHypothesisCannotCreateStudyIdentity ()

missingAbstractDoesNotMeanExclude : MissingAbstractMeansExclude → ⊥
missingAbstractDoesNotMeanExclude ()

screeningDecisionCannotCreateAuditAdmission :
  ScreeningDecisionCreatesAuditAdmission → ⊥
screeningDecisionCannotCreateAuditAdmission ()

slrReviewCannotCreateAuditAdmission : SLRReviewCreatesAuditAdmission → ⊥
slrReviewCannotCreateAuditAdmission ()

paretoBoundaryAnchor : Pareto.AdmissibleConsumerMDLBoundary
paretoBoundaryAnchor = Pareto.canonicalAdmissibleConsumerMDLBoundary

screeningBoundaryAnchor : Screen.ScreeningBoundary
screeningBoundaryAnchor = Screen.canonicalScreeningBoundary

searchAuditBoundaryAnchor : Audit.SearchAuditWeldBoundary
searchAuditBoundaryAnchor = Audit.canonicalSearchAuditWeldBoundary

situatedObserverBoundaryAnchor : Situated.SituatedObserverBoundary
situatedObserverBoundaryAnchor = Situated.canonicalSituatedObserverBoundary


eligibilityFrameBoundaryAnchor : Frame.EligibilityFrameBoundary
eligibilityFrameBoundaryAnchor = Frame.canonicalEligibilityFrameBoundary
