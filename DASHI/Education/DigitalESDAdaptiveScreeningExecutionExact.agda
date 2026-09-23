module DASHI.Education.DigitalESDAdaptiveScreeningExecutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDAdaptiveScreeningProgrammeExact as P0
import DASHI.Education.DigitalESDSelectiveFullTextMaterialisationExact as FullText
import DASHI.Education.DigitalESDFullTextSLRParseExact as Parse
import DASHI.Education.DigitalESDStudyProcessingCensusExact as Census

------------------------------------------------------------------------
-- ITERATIVE DIGITAL-ESD SCREEN -> RETRIEVE -> PARSE EXECUTION
--
-- Runtime owners:
--   interop_scripts/digital_esd/run_screen_review_retrieve_parse_loop.py
--   interop_scripts/digital_esd/fetch_retrieval_residual.py
--
-- The execution loop composes existing authoritative owners:
--
--   candidate/Pareto review packet
--      -> explicit reviewed screening overlay
--      -> authoritative screening ledger
--      -> 43,996-row processing census
--      -> retained-only retrieval residual
--      -> bounded transport
--      -> verified full-text gate
--      -> verified full-text parser handoff
--      -> refreshed processing census
--
-- It does not add a new screening authority or parser semantics.
------------------------------------------------------------------------

adaptiveProgrammeAnchor : P0.AdaptiveScreeningBoundary
adaptiveProgrammeAnchor = P0.canonicalAdaptiveScreeningBoundary

sparseFullTextAnchor : FullText.SparseMaterialisationBoundary
sparseFullTextAnchor = FullText.canonicalSparseMaterialisationBoundary

studyCensusAnchor : Census.StudyProcessingCensusBoundary
studyCensusAnchor = Census.canonicalStudyProcessingCensusBoundary

record ReviewBatchExecutionReceipt : Set where
  constructor review-batch-execution-receipt
  field
    inputAuthoritativeLedgerReference : String
    inputAuthoritativeLedgerSha256 : String
    reviewPacketReference : String
    reviewPacketSha256 : String
    explicitDecisionOverlayReference : String
    explicitDecisionOverlaySha256 : String

    outputAuthoritativeLedgerReference : String
    outputAuthoritativeLedgerSha256 : String

    inputDenominatorCount : Nat
    outputDenominatorCount : Nat
    denominatorCountPreserved :
      outputDenominatorCount ≡ inputDenominatorCount

    explicitReviewedDecisionCount : Nat
    candidateRecommendationCount : Nat

    candidateRecommendationsAutoPromoted : Bool
    candidateRecommendationsAutoPromotedIsFalse :
      candidateRecommendationsAutoPromoted ≡ false

open ReviewBatchExecutionReceipt public

record RetrievalBatchExecutionReceipt : Set where
  constructor retrieval-batch-execution-receipt
  field
    processingLedgerReference : String
    processingLedgerSha256 : String
    retrievalResidualReference : String
    retrievalResidualSha256 : String

    selectedForRetrieval : Nat
    downloadedArtifacts : Nat
    unresolvedRetrievals : Nat

    persistentRetrievedManifestReference : String
    persistentRetrievedManifestSha256 : String
    verifiedFullTextIndexReference : String
    verifiedFullTextIndexSha256 : String

    onlyAuthoritativelyRetainedQueued : Bool
    onlyAuthoritativelyRetainedQueuedIsTrue :
      onlyAuthoritativelyRetainedQueued ≡ true

    transportCreatesScreeningDecision : Bool
    transportCreatesScreeningDecisionIsFalse :
      transportCreatesScreeningDecision ≡ false

    transportCreatesReviewedEvidence : Bool
    transportCreatesReviewedEvidenceIsFalse :
      transportCreatesReviewedEvidence ≡ false

open RetrievalBatchExecutionReceipt public

record ParseBatchExecutionReceipt : Set where
  constructor parse-batch-execution-receipt
  field
    verifiedFullTextIndexReference : String
    parseRunReference : String
    parseRunSha256 : String

    verifiedArtifactCount : Nat
    parserInputCount : Nat
    successfulParseCount : Nat

    processingLedgerReference : String
    processingLedgerSha256 : String

    verifiedArtifactMeansParsed : Bool
    verifiedArtifactMeansParsedIsFalse :
      verifiedArtifactMeansParsed ≡ false

    parseCreatesReviewedEvidence : Bool
    parseCreatesReviewedEvidenceIsFalse :
      parseCreatesReviewedEvidence ≡ false

    parseCreatesSourceAuditAdmission : Bool
    parseCreatesSourceAuditAdmissionIsFalse :
      parseCreatesSourceAuditAdmission ≡ false

open ParseBatchExecutionReceipt public

record AdaptiveScreeningExecutionBoundary : Set where
  constructor adaptive-screening-execution-boundary
  field
    processingDenominatorPreserved : Bool
    processingDenominatorPreservedIsTrue :
      processingDenominatorPreserved ≡ true

    reviewBatchRequiresExplicitDecisionOverlay : Bool
    reviewBatchRequiresExplicitDecisionOverlayIsTrue :
      reviewBatchRequiresExplicitDecisionOverlay ≡ true

    candidateRecommendationIsAuthority : Bool
    candidateRecommendationIsAuthorityIsFalse :
      candidateRecommendationIsAuthority ≡ false

    retrievalResidualRequiresRetainedDecision : Bool
    retrievalResidualRequiresRetainedDecisionIsTrue :
      retrievalResidualRequiresRetainedDecision ≡ true

    metadataOnlyUnreviewedIsRetrievalFailure : Bool
    metadataOnlyUnreviewedIsRetrievalFailureIsFalse :
      metadataOnlyUnreviewedIsRetrievalFailure ≡ false

    retrievalBatchBounded : Bool
    retrievalBatchBoundedIsTrue :
      retrievalBatchBounded ≡ true

    retrievedBytesRequireDigestVerification : Bool
    retrievedBytesRequireDigestVerificationIsTrue :
      retrievedBytesRequireDigestVerification ≡ true

    verifiedBytesAreParsed : Bool
    verifiedBytesAreParsedIsFalse :
      verifiedBytesAreParsed ≡ false

    parseIsReviewedEvidence : Bool
    parseIsReviewedEvidenceIsFalse :
      parseIsReviewedEvidence ≡ false

    reviewedEvidenceIsAdmission : Bool
    reviewedEvidenceIsAdmissionIsFalse :
      reviewedEvidenceIsAdmission ≡ false

open AdaptiveScreeningExecutionBoundary public

canonicalAdaptiveScreeningExecutionBoundary :
  AdaptiveScreeningExecutionBoundary
canonicalAdaptiveScreeningExecutionBoundary =
  adaptive-screening-execution-boundary
    true refl
    true refl
    false refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CandidateRecommendationCreatesAuthoritativeDecision : Set where
data UnreviewedMetadataEntersRetrievalResidual : Set where
data MetadataOnlyUnreviewedCountsAsRetrievalFailure : Set where
data RetrievalCreatesScreeningDecision : Set where
data RetrievalCreatesReviewedEvidence : Set where
data RetrievedBytesCreateSourceTruth : Set where
data VerifiedFullTextCreatesParseReceipt : Set where
data ParseCreatesReviewedEvidence : Set where
data ParseCreatesSourceAuditAdmission : Set where
data LaterStageCreatesEarlierStageWithoutReceipt : Set where

candidateRecommendationDoesNotCreateAuthoritativeDecision :
  CandidateRecommendationCreatesAuthoritativeDecision → ⊥
candidateRecommendationDoesNotCreateAuthoritativeDecision ()

unreviewedMetadataDoesNotEnterRetrievalResidual :
  UnreviewedMetadataEntersRetrievalResidual → ⊥
unreviewedMetadataDoesNotEnterRetrievalResidual ()

metadataOnlyUnreviewedDoesNotCountAsRetrievalFailure :
  MetadataOnlyUnreviewedCountsAsRetrievalFailure → ⊥
metadataOnlyUnreviewedDoesNotCountAsRetrievalFailure ()

retrievalDoesNotCreateScreeningDecision :
  RetrievalCreatesScreeningDecision → ⊥
retrievalDoesNotCreateScreeningDecision ()

retrievalDoesNotCreateReviewedEvidence :
  RetrievalCreatesReviewedEvidence → ⊥
retrievalDoesNotCreateReviewedEvidence ()

retrievedBytesDoNotCreateSourceTruth :
  RetrievedBytesCreateSourceTruth → ⊥
retrievedBytesDoNotCreateSourceTruth ()

verifiedFullTextDoesNotCreateParseReceipt :
  VerifiedFullTextCreatesParseReceipt → ⊥
verifiedFullTextDoesNotCreateParseReceipt ()

parseDoesNotCreateReviewedEvidence :
  ParseCreatesReviewedEvidence → ⊥
parseDoesNotCreateReviewedEvidence ()

parseDoesNotCreateSourceAuditAdmission :
  ParseCreatesSourceAuditAdmission → ⊥
parseDoesNotCreateSourceAuditAdmission ()

laterStageDoesNotCreateEarlierStageWithoutReceipt :
  LaterStageCreatesEarlierStageWithoutReceipt → ⊥
laterStageDoesNotCreateEarlierStageWithoutReceipt ()

adaptiveScreeningExecutionReading : String
adaptiveScreeningExecutionReading =
  "Digital-ESD executes screening as an iterative authority-preserving loop: candidate/Pareto review packets remain advisory; only explicit reviewed overlays modify the authoritative screening ledger; the complete 43,996-record denominator is retained in the processing census; only reviewed include/probable rows enter the full-text retrieval residual; retrieval is bounded and digest-verified; verified bytes remain distinct from parser receipts; parsing remains distinct from reviewed canonical evidence and SourceAuditAdmission. Newly reviewed retained studies therefore enqueue further full-text retrieval, and newly verified artifacts may be parsed immediately without relabelling unresolved metadata as retrieval or parse failures."
