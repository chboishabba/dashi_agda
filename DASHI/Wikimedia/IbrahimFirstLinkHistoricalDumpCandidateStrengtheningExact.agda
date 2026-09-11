module DASHI.Wikimedia.IbrahimFirstLinkHistoricalDumpCandidateStrengtheningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.IbrahimFirstLinkHistoricalSnapshotProvenanceResidualExact as Historical

------------------------------------------------------------------------
-- THIN DELTA: STRONGEST CONCRETE HISTORICAL DUMP CANDIDATE
--
-- Existing owner already retains the November-2014 publication/blog cue and
-- the parser's explicit enwiki/20141008 directory cue without collapsing them.
-- This delta narrows the concrete acquisition target to the exact October file
-- named by contemporaneous external usage and records the producer README's
-- 112-chunk local lineage.  Candidate existence != published-input identity.
------------------------------------------------------------------------

historicalBoundary : Historical.HistoricalSnapshotProvenanceBoundary
historicalBoundary = Historical.canonicalHistoricalSnapshotProvenanceBoundary

producerReadmeSource : Attribution.AttributedSource
producerReadmeSource = Attribution.mkNoDOISource
  "Mark Ibrahim"
  "code/readme.md"
  "marksibrahim/wikipedia_network; blob 9f7bf34feebec01d1166df83846c99a8eda3452c"
  "2015"
  "https://github.com/marksibrahim/wikipedia_network/blob/master/code/readme.md"
  (Attribution.namedSourceKind "research code README")
  "states that the whole Wikipedia XML dump was chopped into local small*.xml pieces; constructor later enumerates 112 pieces; filename prose is vague/inconsistent and does not identify the published input"
  Attribution.publicAttribution

parserRepositorySource : Attribution.AttributedSource
parserRepositorySource = Historical.firstLinkParserSource

constructorRepositorySource : Attribution.AttributedSource
constructorRepositorySource = Historical.flnConstructorSource

record HistoricalDumpCandidateReceipt : Set where
  constructor historical-dump-candidate-receipt
  field
    candidateDirectory : String
    candidateCompressedFilename : String
    candidateDecompressedFilename : String
    parserExplicitlyNamesDirectory : Bool
    contemporaneousExternalUseConfirmsArtifactName : Bool
    producerReadmeConfirmsWholeDumpWasChopped : Bool
    constructorConfirms112LocalChunks : Bool
    exactSplitCommandRecovered : Bool
    exactChunkHashesRecovered : Bool
    candidateHashRecovered : Bool
    candidateSameObjectAsPublishedFLNInput : Bool
    novemberPublicationCueRetained : Bool
    candidateMayEraseNovemberCue : Bool
open HistoricalDumpCandidateReceipt public

strongestConcreteDumpCandidate : HistoricalDumpCandidateReceipt
strongestConcreteDumpCandidate = historical-dump-candidate-receipt
  "https://dumps.wikimedia.org/enwiki/20141008/"
  "enwiki-20141008-pages-articles.xml.bz2"
  "enwiki-20141008-pages-articles.xml"
  true
  true
  true
  true
  false
  false
  false
  false
  true
  false

------------------------------------------------------------------------
-- Payment state: concrete candidate paid; execution lineage still unpaid.
------------------------------------------------------------------------

data CandidateStage : Set where
  directoryCandidatePaid : CandidateStage
  filenameCandidatePaid : CandidateStage
  artifactHashUnpaid : CandidateStage
  dumpToChunksLineageUnpaid : CandidateStage
  parserExecutionUnpaid : CandidateStage
  resultSameObjectUnpaid : CandidateStage

record CandidateStrengtheningBoundary : Set where
  constructor candidate-strengthening-boundary
  field
    october08IsStrongestConcreteRuntimeCandidate : Bool
    october08IsProvenPublishedRuntime : Bool
    exactCompressedFilenameCandidateRecorded : Bool
    producer112ChunkLineageRecorded : Bool
    exactSplitLineageStillRequired : Bool
    exactArtifactHashStillRequired : Bool
    parserEquivalentReproductionStillRequired : Bool
    publishedGraphSameObjectStillRequired : Bool
    novemberPublicationCueStillRetained : Bool
    sourceContradictionDeclaredResolved : Bool
open CandidateStrengtheningBoundary public

canonicalCandidateStrengtheningBoundary : CandidateStrengtheningBoundary
canonicalCandidateStrengtheningBoundary = candidate-strengthening-boundary
  true false true true true true true true true false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data CandidateFilenameMeansExecutedInput : Set where
data ExistingArtifactMeansPublishedSameObject : Set where
data ProducerDirectoryCommentMeansExactHash : Set where
data ChunkCountMeansRecoveredSplitLineage : Set where
data OctoberCandidateCancelsNovemberPublicationDescription : Set where

candidateFilenameDoesNotMeanExecutedInput : CandidateFilenameMeansExecutedInput → ⊥
candidateFilenameDoesNotMeanExecutedInput ()

artifactExistenceDoesNotMeanPublishedSameObject : ExistingArtifactMeansPublishedSameObject → ⊥
artifactExistenceDoesNotMeanPublishedSameObject ()

producerDirectoryCommentDoesNotMeanExactHash : ProducerDirectoryCommentMeansExactHash → ⊥
producerDirectoryCommentDoesNotMeanExactHash ()

chunkCountDoesNotRecoverSplitLineage : ChunkCountMeansRecoveredSplitLineage → ⊥
chunkCountDoesNotRecoverSplitLineage ()

octoberCandidateDoesNotEraseNovemberDescription : OctoberCandidateCancelsNovemberPublicationDescription → ⊥
octoberCandidateDoesNotEraseNovemberDescription ()

remainingHistoricalPayment : String
remainingHistoricalPayment =
  "acquire an authoritative copy or manifest for enwiki-20141008-pages-articles.xml.bz2 and its hash; recover or reconstruct the exact dump-to-112-small*.xml split lineage; execute the pinned parser/constructor equivalently; compare the reproduced FLN against the author-hosted fln.json/result object. Until then 2014-10-08 is the strongest concrete input candidate, not a promoted published-runtime identity."
