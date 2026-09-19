module DASHI.Education.DigitalESDAdaptiveScreeningProgrammeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Pareto
import DASHI.Core.NDimParetoHyperfabricExact as NDim
import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Education.DigitalESDTitleAbstractScreeningExact as Screen
import DASHI.Education.DigitalESDEligibilityFrameExclusionExact as Frame
import DASHI.Education.DigitalESDSearchToSourceAuditAdmissionExact as SearchAudit
import DASHI.Education.DigitalESDSLRSourceReviewBridgeExact as SLR
import DASHI.Education.DigitalESDSourceAuditAdmissionExact as Audit

------------------------------------------------------------------------
-- DIGITAL-ESD P0-A ... P0-G ADAPTIVE SCREENING PROGRAMME
--
-- Existing owners remain authoritative:
--
--   ScreeningDecisionReceipt / ScreeningLedgerReceipt
--       DigitalESDTitleAbstractScreeningExact
--
--   upstream eligibility-frame nonfactorability
--       DigitalESDEligibilityFrameExclusionExact
--
--   Pareto order / consumer-relative ranking
--       AdmissibleConsumerMDLHyperfabricExact
--       NDimParetoHyperfabricExact
--
--   search lineage / audit admission / SLR full-text review
--       DigitalESDSearchToSourceAuditAdmissionExact
--       DigitalESDSLRSourceReviewBridgeExact
--
-- This owner adds only the lower-authority adaptive queue machinery needed
-- between the exact deduplicated universe and those existing downstream
-- authorities.
------------------------------------------------------------------------

screeningAuthority : Screen.ScreeningBoundary
screeningAuthority = Screen.canonicalScreeningBoundary

eligibilityFrameAuthority : Frame.EligibilityFrameBoundary
eligibilityFrameAuthority = Frame.canonicalEligibilityFrameBoundary

------------------------------------------------------------------------
-- P0-A — denominator integrity over the exact screening universe.
------------------------------------------------------------------------

data ReviewCoverageState : Set where
  pendingReview : ReviewCoverageState
  reviewedDecision : Screen.ScreeningDecision → ReviewCoverageState

record ScreeningUniverse : Set₁ where
  constructor screening-universe
  field
    Record : Set
    sourceIdentityReference : Record → String
    metadataRevisionReference : Record → String
    coverageState : Record → ReviewCoverageState

    exactDeduplicatedSetReference : String
    exactDeduplicatedSetSha256 : String
    exactRecordCountReference : String
    screeningLedger : Screen.ScreeningLedgerReceipt

    everyRecordHasCoverageState : Bool
    everyRecordHasCoverageStateIsTrue :
      everyRecordHasCoverageState ≡ true

    pendingRecordsRemainInDenominator : Bool
    pendingRecordsRemainInDenominatorIsTrue :
      pendingRecordsRemainInDenominator ≡ true

open ScreeningUniverse public

record ScreeningUniverseRuntimeReceipt : Set where
  constructor screening-universe-runtime-receipt
  field
    exactInputArtifactReference : String
    exactInputSha256 : String
    inputRecordCount : Nat
    unresolvedLedgerReference : String
    unresolvedLedgerSha256 : String
    emittedReceiptCount : Nat
    emittedReceiptCountMatchesInput :
      emittedReceiptCount ≡ inputRecordCount
    runtimeReference : String
    runtimeTimestamp : String
    allInputRecordsReceivedReceipts : Bool
    allInputRecordsReceivedReceiptsIsTrue :
      allInputRecordsReceivedReceipts ≡ true

open ScreeningUniverseRuntimeReceipt public

------------------------------------------------------------------------
-- P0-B — candidate assessment is advisory evidence, never screening authority.
------------------------------------------------------------------------

record ScreeningCandidateAssessment : Set where
  constructor screening-candidate-assessment
  field
    sourceIdentityReference : String
    metadataRevisionReference : String
    titleAbstractSnapshotReference : String
    rubricVersion : String

    candidateDecision : Screen.ScreeningDecision
    candidateReasonCodes : List Screen.ScreeningReasonCode
    featureEvidenceReferences : List String

    modelOrProcessReference : String
    confidenceReference : String
    marginReference : String
    assessmentReference : String
    assessmentTimestamp : String

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    explicitlyReviewed : Bool
    explicitlyReviewedIsFalse : explicitlyReviewed ≡ false

    createsScreeningDecision : Bool
    createsScreeningDecisionIsFalse : createsScreeningDecision ≡ false
    createsExclusion : Bool
    createsExclusionIsFalse : createsExclusion ≡ false
    createsSourceTruth : Bool
    createsSourceTruthIsFalse : createsSourceTruth ≡ false

open ScreeningCandidateAssessment public


------------------------------------------------------------------------
-- Constructive non-factorability: candidate assessment cannot determine the
-- authoritative reviewed screening decision.
------------------------------------------------------------------------

data CandidateAssessmentWorld : Set where
  sameCandidateSurfaceReviewedInclude : CandidateAssessmentWorld
  sameCandidateSurfaceReviewedExclude : CandidateAssessmentWorld

data CandidateAssessmentSurface : Set where
  sameCandidateAssessmentSurface : CandidateAssessmentSurface

candidateAssessmentProjection :
  CandidateAssessmentWorld → CandidateAssessmentSurface
candidateAssessmentProjection sameCandidateSurfaceReviewedInclude =
  sameCandidateAssessmentSurface
candidateAssessmentProjection sameCandidateSurfaceReviewedExclude =
  sameCandidateAssessmentSurface

reviewedScreeningOutcome :
  CandidateAssessmentWorld → Screen.ScreeningDecision
reviewedScreeningOutcome sameCandidateSurfaceReviewedInclude = Screen.include
reviewedScreeningOutcome sameCandidateSurfaceReviewedExclude = Screen.exclude

reviewedOutcomesDiffer :
  reviewedScreeningOutcome sameCandidateSurfaceReviewedInclude ≡
  reviewedScreeningOutcome sameCandidateSurfaceReviewedExclude → ⊥
reviewedOutcomesDiffer ()

candidateAssessmentNonFactorWitness :
  NonFactor.NonFactorabilityWitness
    candidateAssessmentProjection
    reviewedScreeningOutcome
candidateAssessmentNonFactorWitness =
  NonFactor.nonFactorabilityWitness
    sameCandidateSurfaceReviewedInclude
    sameCandidateSurfaceReviewedExclude
    refl
    reviewedOutcomesDiffer

CandidateAssessmentFactorisation : Set₁
CandidateAssessmentFactorisation =
  NonFactor.FactorsThrough
    candidateAssessmentProjection
    reviewedScreeningOutcome

candidateAssessmentCannotDetermineReviewedDecision :
  CandidateAssessmentFactorisation → ⊥
candidateAssessmentCannotDetermineReviewedDecision =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    candidateAssessmentNonFactorWitness

------------------------------------------------------------------------
-- Constructive non-factorability: a similarity/family surface cannot determine
-- whether two publications instantiate the same empirical study.
------------------------------------------------------------------------

data FamilySimilarityWorld : Set where
  sameSimilaritySameStudy : FamilySimilarityWorld
  sameSimilarityDifferentStudy : FamilySimilarityWorld

data FamilySimilaritySurface : Set where
  sameFamilySimilaritySurface : FamilySimilaritySurface

familySimilarityProjection :
  FamilySimilarityWorld → FamilySimilaritySurface
familySimilarityProjection sameSimilaritySameStudy =
  sameFamilySimilaritySurface
familySimilarityProjection sameSimilarityDifferentStudy =
  sameFamilySimilaritySurface

sameEmpiricalStudyState : FamilySimilarityWorld → Bool
sameEmpiricalStudyState sameSimilaritySameStudy = true
sameEmpiricalStudyState sameSimilarityDifferentStudy = false

studyIdentityStatesDiffer :
  sameEmpiricalStudyState sameSimilaritySameStudy ≡
  sameEmpiricalStudyState sameSimilarityDifferentStudy → ⊥
studyIdentityStatesDiffer ()

familySimilarityNonFactorWitness :
  NonFactor.NonFactorabilityWitness
    familySimilarityProjection
    sameEmpiricalStudyState
familySimilarityNonFactorWitness =
  NonFactor.nonFactorabilityWitness
    sameSimilaritySameStudy
    sameSimilarityDifferentStudy
    refl
    studyIdentityStatesDiffer

FamilySimilarityFactorisation : Set₁
FamilySimilarityFactorisation =
  NonFactor.FactorsThrough
    familySimilarityProjection
    sameEmpiricalStudyState

familySimilarityCannotDetermineSameEmpiricalStudy :
  FamilySimilarityFactorisation → ⊥
familySimilarityCannotDetermineSameEmpiricalStudy =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    familySimilarityNonFactorWitness

------------------------------------------------------------------------
-- Review-process missingness / frame probes.
------------------------------------------------------------------------

data ScreeningProcessAbsenceProbe : Set where
  inspectSearchVocabularyExclusion
  inspectMissingAbstractOrMetadata
  inspectSystematicDeprioritisation
  inspectUnderrepresentedSourceTypes
  inspectTerminologyOutsideFrozenQueries
  : ScreeningProcessAbsenceProbe

screeningProcessProbeReading : ScreeningProcessAbsenceProbe → String
screeningProcessProbeReading inspectSearchVocabularyExclusion =
  "inspect which potentially relevant populations, practices or source genres could not enter the retrieved universe because the frozen search vocabulary did not name them"
screeningProcessProbeReading inspectMissingAbstractOrMetadata =
  "inspect records whose title/abstract or metadata are absent, malformed or too sparse for the same screening process"
screeningProcessProbeReading inspectSystematicDeprioritisation =
  "inspect whether a candidate-ranking process repeatedly delays particular populations, terminologies, source roles or publication forms"
screeningProcessProbeReading inspectUnderrepresentedSourceTypes =
  "inspect source types or publication forms that occupy sparse cells in the retrieved/screened carrier"
screeningProcessProbeReading inspectTerminologyOutsideFrozenQueries =
  "inspect terminology used by relevant communities or disciplines that falls outside the seven frozen query families"

------------------------------------------------------------------------
-- P0-C — record/report/study-family hypotheses remain hypotheses.
------------------------------------------------------------------------

record StudyFamilyHypothesis : Set where
  constructor study-family-hypothesis
  field
    leftSourceIdentityReference : String
    rightSourceIdentityReference : String
    proposedRelation : Screen.DuplicateRelationKind

    doiEvidenceReference : String
    titleEvidenceReference : String
    authorEvidenceReference : String
    yearEvidenceReference : String
    institutionEvidenceReference : String
    sampleEvidenceReference : String
    countryEvidenceReference : String
    interventionEvidenceReference : String
    abstractSimilarityReference : String
    accessionRelationReference : String

    hypothesisReference : String
    processReference : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    createsDuplicateDecision : Bool
    createsDuplicateDecisionIsFalse : createsDuplicateDecision ≡ false
    createsSameEmpiricalStudy : Bool
    createsSameEmpiricalStudyIsFalse : createsSameEmpiricalStudy ≡ false

open StudyFamilyHypothesis public

record StudyFamilyCandidateFibre : Set where
  constructor study-family-candidate-fibre
  field
    fibreReference : String
    representativeSourceReference : String
    memberSourceReferences : List String
    hypothesisReferences : List String
    reviewedAsSameEmpiricalStudy : Bool
    reviewedAsSameEmpiricalStudyIsFalse :
      reviewedAsSameEmpiricalStudy ≡ false

open StudyFamilyCandidateFibre public

------------------------------------------------------------------------
-- P0-D — calibration strata.
------------------------------------------------------------------------

data CalibrationStratum : Set where
  obviousIncludeCandidate
  obviousExcludeCandidate
  highUncertaintyCandidate
  highDuplicateAmbiguity
  rareTerminologyOrSourceType
  missingAbstractOrMalformedMetadata
  : CalibrationStratum

record CalibrationSelectionReceipt : Set where
  constructor calibration-selection-receipt
  field
    sourceIdentityReference : String
    stratum : CalibrationStratum
    stratumEvidenceReference : String
    selectionReference : String
    selectionProcessReference : String
    selectedForExplicitReview : Bool
    selectedForExplicitReviewIsTrue :
      selectedForExplicitReview ≡ true
    selectionCreatesDecision : Bool
    selectionCreatesDecisionIsFalse :
      selectionCreatesDecision ≡ false

open CalibrationSelectionReceipt public

------------------------------------------------------------------------
-- P0-E — calibration estimates remain bounded diagnostics.
------------------------------------------------------------------------

record ScreeningCalibrationEstimate : Set where
  constructor screening-calibration-estimate
  field
    reviewedCalibrationSetReference : String
    reviewedCalibrationSetSha256 : String
    rubricVersion : String

    falseNegativeRiskEstimateReference : String
    reviewerDisagreementReference : String
    rubricAmbiguityReference : String
    residualClassReference : String
    estimateScopeReference : String
    estimatorOrProcessReference : String

    estimateCreatesSourceTruth : Bool
    estimateCreatesSourceTruthIsFalse :
      estimateCreatesSourceTruth ≡ false
    estimateCreatesPopulationTruth : Bool
    estimateCreatesPopulationTruthIsFalse :
      estimateCreatesPopulationTruth ≡ false
    estimateCreatesAutomaticDecision : Bool
    estimateCreatesAutomaticDecisionIsFalse :
      estimateCreatesAutomaticDecision ≡ false

open ScreeningCalibrationEstimate public

------------------------------------------------------------------------
-- P0-F — fail-closed Pareto work-queue selection.
--
-- The repo-native Pareto order is lower-is-better.  Benefits are therefore
-- represented as externally computed loss/cost coordinates rather than being
-- scalarised into one score.
------------------------------------------------------------------------

record ScreeningQueueCandidate : Set where
  constructor screening-queue-candidate
  field
    sourceIdentityReference : String
    candidateAssessmentReference : String
    familyHypothesisReference : String
    calibrationStratumReference : String

    informationGainLossCost : Nat
    corpusContractionLossCost : Nat
    rareCellCoverageLossCost : Nat
    duplicateFamilyPayoffLossCost : Nat
    reviewerCost : Nat

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    pendingExplicitReview : Bool
    pendingExplicitReviewIsTrue : pendingExplicitReview ≡ true

open ScreeningQueueCandidate public

data ScreeningPriorityAxis : Set where
  informationGainAxis
  corpusContractionAxis
  rareCellCoverageAxis
  duplicateFamilyPayoffAxis
  reviewerCostAxis
  : ScreeningPriorityAxis

screeningQueueProblem : Pareto.ConsumerMDLProblem
screeningQueueProblem =
  Pareto.consumerMDLProblem
    ScreeningQueueCandidate
    (λ _ → ⊤)
    (λ _ → ⊤)
    reviewerCost
    (λ _ _ → ⊤)
    sourceIdentityReference
    "Digital-ESD adaptive screening reviewer-cost convention; costs rank work only"
    "explicit title/abstract review prioritisation"

screeningPriorityCosts : Pareto.CostHyperfabric screeningQueueProblem
screeningPriorityCosts =
  Pareto.costHyperfabric ScreeningPriorityAxis axisCost axisReference
  where
  axisCost : ScreeningPriorityAxis → ScreeningQueueCandidate → Nat
  axisCost informationGainAxis = informationGainLossCost
  axisCost corpusContractionAxis = corpusContractionLossCost
  axisCost rareCellCoverageAxis = rareCellCoverageLossCost
  axisCost duplicateFamilyPayoffAxis = duplicateFamilyPayoffLossCost
  axisCost reviewerCostAxis = reviewerCost

  axisReference : ScreeningPriorityAxis → String
  axisReference informationGainAxis = "information-gain loss"
  axisReference corpusContractionAxis = "likely corpus-contraction loss"
  axisReference rareCellCoverageAxis = "rare-cell coverage loss"
  axisReference duplicateFamilyPayoffAxis = "duplicate-family payoff loss"
  axisReference reviewerCostAxis = "reviewer cost"

ScreeningParetoSelection : ScreeningQueueCandidate → Set₁
ScreeningParetoSelection =
  Pareto.ParetoAdmissible screeningPriorityCosts

screeningParetoView : NDim.NDimParetoView screeningPriorityCosts
screeningParetoView =
  NDim.ndimParetoView
    5
    "five declared screening-priority axes"
    axisReference
    true
    "non-scalar Pareto frontier; visualisation optional"
  where
  axisReference : ScreeningPriorityAxis → String
  axisReference informationGainAxis = "information gain"
  axisReference corpusContractionAxis = "corpus contraction"
  axisReference rareCellCoverageAxis = "rare-cell coverage"
  axisReference duplicateFamilyPayoffAxis = "duplicate-family payoff"
  axisReference reviewerCostAxis = "reviewer cost"

record ScreeningPriorityReceipt : Set where
  constructor screening-priority-receipt
  field
    candidate : ScreeningQueueCandidate
    paretoReference : String
    priorityBatchReference : String
    rankOrFrontierReference : String
    selectionCreatesScreeningDecision : Bool
    selectionCreatesScreeningDecisionIsFalse :
      selectionCreatesScreeningDecision ≡ false
    selectionCreatesExclusion : Bool
    selectionCreatesExclusionIsFalse :
      selectionCreatesExclusion ≡ false

open ScreeningPriorityReceipt public

------------------------------------------------------------------------
-- P0-G — only reviewed include/probable decisions may escalate to full text.
------------------------------------------------------------------------

data RetainedForFullText : Screen.ScreeningDecision → Set where
  includeRetained : RetainedForFullText Screen.include
  probableRetained : RetainedForFullText Screen.probable

record FullTextEscalationReceipt : Set where
  constructor full-text-escalation-receipt
  field
    screeningDecision : Screen.ScreeningDecisionReceipt
    retained :
      RetainedForFullText (Screen.decision screeningDecision)

    fullTextRequestReference : String
    fullTextRetrievalProcessReference : String
    retrievalStatusReference : String
    escalationReference : String

    retrievalCreatesSourceTruth : Bool
    retrievalCreatesSourceTruthIsFalse :
      retrievalCreatesSourceTruth ≡ false
    retrievalCreatesSourceAuditAdmission : Bool
    retrievalCreatesSourceAuditAdmissionIsFalse :
      retrievalCreatesSourceAuditAdmission ≡ false

open FullTextEscalationReceipt public

record CanonicalFullTextReviewCarrier
    (source : Attr.AttributedSource) : Set where
  constructor canonical-full-text-review-carrier
  field
    fullTextArtifact : SLR.FullTextArtifactReceipt source
    slrReviewPacket : SLR.SLRSourceReviewPacket source

    screeningStillDistinctFromAudit : Bool
    screeningStillDistinctFromAuditIsTrue :
      screeningStillDistinctFromAudit ≡ true

open CanonicalFullTextReviewCarrier public

record P0GAdmittedAuditedCarrier
    (source : Attr.AttributedSource) : Set where
  constructor p0g-admitted-audited-carrier
  field
    canonicalReview : CanonicalFullTextReviewCarrier source
    sourceAuditAdmission : Audit.SourceAuditAdmission source
    corpusAuditedSource : SearchAudit.CorpusAuditedSource source

open P0GAdmittedAuditedCarrier public

------------------------------------------------------------------------
-- Phase / denominator firewalls.
------------------------------------------------------------------------

data CandidateAssessmentCreatesScreeningDecision : Set where
data CandidateAssessmentCreatesExclusion : Set where
data StudyFamilyHypothesisCreatesSameEmpiricalStudy : Set where
data ParetoPriorityCreatesScreeningDecision : Set where
data ParetoPriorityCreatesExclusion : Set where
data UnreviewedRecordMayLeaveDenominator : Set where
data MissingAbstractCreatesAutomaticExclusion : Set where
data CalibrationEstimateCreatesSourceTruth : Set where
data CalibrationEstimateCreatesPopulationTruth : Set where
data CalibrationEstimateCreatesAutomaticDecision : Set where
data FullTextRetrievalCreatesSourceAuditAdmission : Set where
data FullTextRetrievalCreatesSourceTruth : Set where
data ScreeningSelectionCreatesEligibilityFrameTruth : Set where
data ScreeningPriorityScoreCreatesSourceQuality : Set where

candidateAssessmentDoesNotCreateScreeningDecision :
  CandidateAssessmentCreatesScreeningDecision → ⊥
candidateAssessmentDoesNotCreateScreeningDecision ()

candidateAssessmentDoesNotCreateExclusion :
  CandidateAssessmentCreatesExclusion → ⊥
candidateAssessmentDoesNotCreateExclusion ()

studyFamilyHypothesisDoesNotCreateSameEmpiricalStudy :
  StudyFamilyHypothesisCreatesSameEmpiricalStudy → ⊥
studyFamilyHypothesisDoesNotCreateSameEmpiricalStudy ()

paretoPriorityDoesNotCreateScreeningDecision :
  ParetoPriorityCreatesScreeningDecision → ⊥
paretoPriorityDoesNotCreateScreeningDecision ()

paretoPriorityDoesNotCreateExclusion :
  ParetoPriorityCreatesExclusion → ⊥
paretoPriorityDoesNotCreateExclusion ()

unreviewedRecordDoesNotLeaveDenominator :
  UnreviewedRecordMayLeaveDenominator → ⊥
unreviewedRecordDoesNotLeaveDenominator ()

missingAbstractDoesNotCreateAutomaticExclusion :
  MissingAbstractCreatesAutomaticExclusion → ⊥
missingAbstractDoesNotCreateAutomaticExclusion ()

calibrationEstimateDoesNotCreateSourceTruth :
  CalibrationEstimateCreatesSourceTruth → ⊥
calibrationEstimateDoesNotCreateSourceTruth ()

calibrationEstimateDoesNotCreatePopulationTruth :
  CalibrationEstimateCreatesPopulationTruth → ⊥
calibrationEstimateDoesNotCreatePopulationTruth ()

calibrationEstimateDoesNotCreateAutomaticDecision :
  CalibrationEstimateCreatesAutomaticDecision → ⊥
calibrationEstimateDoesNotCreateAutomaticDecision ()

fullTextRetrievalDoesNotCreateSourceAuditAdmission :
  FullTextRetrievalCreatesSourceAuditAdmission → ⊥
fullTextRetrievalDoesNotCreateSourceAuditAdmission ()

fullTextRetrievalDoesNotCreateSourceTruth :
  FullTextRetrievalCreatesSourceTruth → ⊥
fullTextRetrievalDoesNotCreateSourceTruth ()

screeningSelectionDoesNotCreateEligibilityFrameTruth :
  ScreeningSelectionCreatesEligibilityFrameTruth → ⊥
screeningSelectionDoesNotCreateEligibilityFrameTruth ()

screeningPriorityScoreDoesNotCreateSourceQuality :
  ScreeningPriorityScoreCreatesSourceQuality → ⊥
screeningPriorityScoreDoesNotCreateSourceQuality ()

------------------------------------------------------------------------
-- Programme state.
------------------------------------------------------------------------

data P0StageState : Set where
  sourceWritten
  implementedAwaitingRuntime
  blockedOnReviewedCorpus
  paid
  : P0StageState

record AdaptiveScreeningProgrammeState : Set where
  constructor adaptive-screening-programme-state
  field
    p0aUniverseLedger : P0StageState
    p0bCandidateAssessment : P0StageState
    p0cStudyFamilyHypotheses : P0StageState
    p0dCalibrationSelection : P0StageState
    p0eCalibrationDiagnostics : P0StageState
    p0fParetoReviewQueue : P0StageState
    p0gFullTextAndCanonicalReview : P0StageState

open AdaptiveScreeningProgrammeState public

canonicalAdaptiveScreeningProgrammeState : AdaptiveScreeningProgrammeState
canonicalAdaptiveScreeningProgrammeState =
  adaptive-screening-programme-state
    implementedAwaitingRuntime
    implementedAwaitingRuntime
    implementedAwaitingRuntime
    implementedAwaitingRuntime
    implementedAwaitingRuntime
    implementedAwaitingRuntime
    blockedOnReviewedCorpus

record AdaptiveScreeningBoundary : Set where
  constructor adaptive-screening-boundary
  field
    usesExistingScreeningLedger : Bool
    usesExistingScreeningLedgerIsTrue :
      usesExistingScreeningLedger ≡ true

    pendingRecordsStayInDenominator : Bool
    pendingRecordsStayInDenominatorIsTrue :
      pendingRecordsStayInDenominator ≡ true

    candidateAssessmentIsDecisionAuthority : Bool
    candidateAssessmentIsDecisionAuthorityIsFalse :
      candidateAssessmentIsDecisionAuthority ≡ false

    familyHypothesisCreatesStudyIdentity : Bool
    familyHypothesisCreatesStudyIdentityIsFalse :
      familyHypothesisCreatesStudyIdentity ≡ false

    calibrationCreatesAutomaticExclusion : Bool
    calibrationCreatesAutomaticExclusionIsFalse :
      calibrationCreatesAutomaticExclusion ≡ false

    usesRepoNativePareto : Bool
    usesRepoNativeParetoIsTrue :
      usesRepoNativePareto ≡ true

    paretoRequiresScalarScore : Bool
    paretoRequiresScalarScoreIsFalse :
      paretoRequiresScalarScore ≡ false

    paretoCreatesScreeningDecision : Bool
    paretoCreatesScreeningDecisionIsFalse :
      paretoCreatesScreeningDecision ≡ false

    slrOnlyAfterRetainedOrProbable : Bool
    slrOnlyAfterRetainedOrProbableIsTrue :
      slrOnlyAfterRetainedOrProbable ≡ true

    sourceAuditAdmissionRemainsIndependent : Bool
    sourceAuditAdmissionRemainsIndependentIsTrue :
      sourceAuditAdmissionRemainsIndependent ≡ true

    upstreamEligibilityFrameRemainsVisible : Bool
    upstreamEligibilityFrameRemainsVisibleIsTrue :
      upstreamEligibilityFrameRemainsVisible ≡ true

open AdaptiveScreeningBoundary public

canonicalAdaptiveScreeningBoundary : AdaptiveScreeningBoundary
canonicalAdaptiveScreeningBoundary =
  adaptive-screening-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl
    false refl
    true refl
    true refl
    true refl

adaptiveScreeningReading : String
adaptiveScreeningReading =
  "Digital-ESD P0-A..P0-G is an epistemically governed adaptive-screening programme over the exact deduplicated corpus. Every input record remains either pending or explicitly reviewed in the authoritative screening ledger. Machine/model candidate assessments, duplicate/study-family hypotheses, calibration diagnostics and Pareto priority receipts are candidate-only work-allocation surfaces and cannot create inclusion, exclusion, source truth, study identity, eligibility-frame truth or SourceAuditAdmission. The queue reuses DASHI's non-scalar N-dimensional Pareto hyperfabric. Only authoritative include/probable screening decisions may escalate to full-text retrieval; canonical SLR review and SourceAuditAdmission remain downstream independent payments."
