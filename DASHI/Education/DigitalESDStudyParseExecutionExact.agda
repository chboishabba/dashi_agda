module DASHI.Education.DigitalESDStudyParseExecutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDStudyParseInteropExact as Parse

------------------------------------------------------------------------
-- DIGITAL-ESD CORPUS-SCALE STUDY PARSE EXECUTION RECEIPTS
--
-- Runtime owner:
--   interop_scripts/digital_esd/run_study_parse_corpus.py
--
-- This module does not claim that the full 43,996-study parse has already
-- executed.  It specifies the exact receipt shape required when it does.
------------------------------------------------------------------------

record StudyParseShardReceipt : Set where
  constructor study-parse-shard-receipt
  field
    shardId : Nat
    purposeReference : String

    sourceUnitCount : Nat
    parserManifestCount : Nat
    retainedStudyPacketCount : Nat
    screeningResolutionPacketCount : Nat

    shardInputReference : String
    shardInputSha256 : String
    parserManifestReference : String
    parserManifestSha256 : String
    parserSummaryReference : String
    parserSummarySha256 : String
    studyPacketsReference : String
    studyPacketsSha256 : String
    resolutionPacketsReference : String
    resolutionPacketsSha256 : String
    studyParseSummaryReference : String
    studyParseSummarySha256 : String

    parserManifestMatchesSourceUnitCount : Bool
    parserManifestMatchesSourceUnitCountIsTrue :
      parserManifestMatchesSourceUnitCount ≡ true

    packetCountMatchesSourceUnitCount : Bool
    packetCountMatchesSourceUnitCountIsTrue :
      packetCountMatchesSourceUnitCount ≡ true

    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    parserSemanticsChanged : Bool
    parserSemanticsChangedIsFalse : parserSemanticsChanged ≡ false

    automaticCoordinatePayment : Bool
    automaticCoordinatePaymentIsFalse :
      automaticCoordinatePayment ≡ false

    sourceAuditAdmissionCreated : Bool
    sourceAuditAdmissionCreatedIsFalse :
      sourceAuditAdmissionCreated ≡ false

open StudyParseShardReceipt public

record StudyParseCorpusExecutionReceipt : Set where
  constructor study-parse-corpus-execution-receipt
  field
    purposeReference : String

    fullTextIndexReference : String
    fullTextIndexSha256 : String

    preparedSourceUnitsReference : String
    preparedSourceUnitsSha256 : String

    sourceUnitCount : Nat
    shardCount : Nat
    parsedSourceCount : Nat
    retainedStudyPacketCount : Nat
    screeningResolutionPacketCount : Nat

    aggregateStudyPacketReference : String
    aggregateStudyPacketSha256 : String
    aggregateResolutionPacketReference : String
    aggregateResolutionPacketSha256 : String

    shardReceiptManifestReference : String
    executionReference : String
    executionTimestamp : String

    allSourceUnitsParsedExactlyOnce : Bool
    allSourceUnitsParsedExactlyOnceIsTrue :
      allSourceUnitsParsedExactlyOnce ≡ true

    aggregatePacketCountMatchesParsedCount : Bool
    aggregatePacketCountMatchesParsedCountIsTrue :
      aggregatePacketCountMatchesParsedCount ≡ true

    everyShardReceiptHashVerified : Bool
    everyShardReceiptHashVerifiedIsTrue :
      everyShardReceiptHashVerified ≡ true

    candidateOnly : Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true

    parserSemanticsChanged : Bool
    parserSemanticsChangedIsFalse :
      parserSemanticsChanged ≡ false

    automaticCoordinatePayment : Bool
    automaticCoordinatePaymentIsFalse :
      automaticCoordinatePayment ≡ false

    corpusExecutionCreatesSourceAuditAdmission : Bool
    corpusExecutionCreatesSourceAuditAdmissionIsFalse :
      corpusExecutionCreatesSourceAuditAdmission ≡ false

open StudyParseCorpusExecutionReceipt public

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record StudyParseExecutionBoundary : Set where
  constructor study-parse-execution-boundary
  field
    usesGenericParserThroughThinInterop : Bool
    usesGenericParserThroughThinInteropIsTrue :
      usesGenericParserThroughThinInterop ≡ true

    deterministicSharding : Bool
    deterministicShardingIsTrue :
      deterministicSharding ≡ true

    resumeRequiresExactShardHashes : Bool
    resumeRequiresExactShardHashesIsTrue :
      resumeRequiresExactShardHashes ≡ true

    allSourceUnitsParsedExactlyOnce : Bool
    allSourceUnitsParsedExactlyOnceIsTrue :
      allSourceUnitsParsedExactlyOnce ≡ true

    aggregateCountsMustReconcile : Bool
    aggregateCountsMustReconcileIsTrue :
      aggregateCountsMustReconcile ≡ true

    parserChangesSemanticAuthority : Bool
    parserChangesSemanticAuthorityIsFalse :
      parserChangesSemanticAuthority ≡ false

    parserPaysExtractionCoordinates : Bool
    parserPaysExtractionCoordinatesIsFalse :
      parserPaysExtractionCoordinates ≡ false

    corpusExecutionCreatesSourceAuditAdmission : Bool
    corpusExecutionCreatesSourceAuditAdmissionIsFalse :
      corpusExecutionCreatesSourceAuditAdmission ≡ false

open StudyParseExecutionBoundary public

canonicalStudyParseExecutionBoundary : StudyParseExecutionBoundary
canonicalStudyParseExecutionBoundary =
  study-parse-execution-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Existing parser interop remains the semantic boundary.
------------------------------------------------------------------------

studyParseInteropBoundary : Parse.StudyParseInteropBoundary
studyParseInteropBoundary = Parse.canonicalStudyParseInteropBoundary

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ShardReceiptCreatesExtractionPayment : Set where
data ShardReceiptCreatesSourceTruth : Set where
data AggregateParsePacketCreatesSourceAuditAdmission : Set where
data ParsedCorpusMeansReviewedCorpus : Set where
data ParsedCorpusMeansAdmittedCorpus : Set where
data ParserCandidateMeansClaimTruth : Set where

shardReceiptDoesNotCreateExtractionPayment :
  ShardReceiptCreatesExtractionPayment → ⊥
shardReceiptDoesNotCreateExtractionPayment ()

shardReceiptDoesNotCreateSourceTruth :
  ShardReceiptCreatesSourceTruth → ⊥
shardReceiptDoesNotCreateSourceTruth ()

aggregateParsePacketDoesNotCreateSourceAuditAdmission :
  AggregateParsePacketCreatesSourceAuditAdmission → ⊥
aggregateParsePacketDoesNotCreateSourceAuditAdmission ()

parsedCorpusDoesNotMeanReviewedCorpus :
  ParsedCorpusMeansReviewedCorpus → ⊥
parsedCorpusDoesNotMeanReviewedCorpus ()

parsedCorpusDoesNotMeanAdmittedCorpus :
  ParsedCorpusMeansAdmittedCorpus → ⊥
parsedCorpusDoesNotMeanAdmittedCorpus ()

parserCandidateDoesNotMeanClaimTruth :
  ParserCandidateMeansClaimTruth → ⊥
parserCandidateDoesNotMeanClaimTruth ()

studyParseExecutionReading : String
studyParseExecutionReading =
  "Digital-ESD corpus-scale parsing deterministically shards the verified full-text source-unit set, invokes the existing generic SLR dependency/PNF parser on each shard, verifies exact shard input/output hashes, and aggregates one candidate packet per parsed source. A shard may be resumed only when the exact input and output hashes still match. Corpus parsing must reconcile source-unit, parser-manifest and aggregate-packet counts exactly. Even a complete parse of every verified study remains candidate-only: parsing pays no extraction coordinate, creates no source truth, reviewed corpus, admitted corpus or SourceAuditAdmission."
