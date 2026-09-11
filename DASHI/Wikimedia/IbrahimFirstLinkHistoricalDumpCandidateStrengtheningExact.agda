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

------------------------------------------------------------------------
-- Independent historical corroboration acquired 2026-09-11.
--
-- These sources pay only artifact/directory existence and filename plausibility.
-- They do NOT pay Ibrahim's executed-input identity, hash, split lineage or
-- result same-object relation.
------------------------------------------------------------------------

contemporaneousUsageSource : Attribution.AttributedSource
contemporaneousUsageSource = Attribution.mkNoDOISource
  "Sanmayce / Tom's Hardware forum"
  "Need assistance in running 16-threaded superheavy fuzzy search"
  "Tom's Hardware Forum"
  "2014-12-22"
  "https://forums.tomshardware.com/threads/need-assistance-in-running-16-threaded-superheavy-fuzzy-search.2075303/"
  (Attribution.namedSourceKind "third-party contemporaneous technical forum post")
  "independently names the URL https://dumps.wikimedia.org/enwiki/20141008/enwiki-20141008-pages-articles.xml.bz2 as downloadable test data shortly after the dump date; corroborates artifact filename/existence only"
  Attribution.publicAttribution

mirrorInventorySource : Attribution.AttributedSource
mirrorInventorySource = Attribution.mkNoDOISource
  "Federal University of Paraná mirror statistics"
  "FTP Site Statistics"
  "wikipedia.c3sl.ufpr.br mirror inventory report"
  "2015-03-15"
  "https://www.ftpstatus.com/reports/wikipedia.c3sl.ufpr.br.pdf"
  (Attribution.namedSourceKind "institutional mirror inventory report")
  "lists /wikipedia/enwiki/20141008 with 548 files and approximately 852.84 GB, corroborating that an October-2014 English Wikipedia dump directory was mirrored; does not identify Ibrahim's exact input or hash"
  Attribution.publicAttribution

record HistoricalDumpCandidateReceipt : Set where
  constructor historical-dump-candidate-receipt
  field
    candidateDirectory : String
    candidateCompressedFilename : String
    candidateDecompressedFilename : String
    parserExplicitlyNamesDirectory : Bool
    contemporaneousExternalUseConfirmsArtifactName : Bool
    independent2014UseConfirmsDownloadableArtifact : Bool
    institutionalMirrorInventoryConfirmsDirectory : Bool
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
  independentExistenceCorroborationPaid : CandidateStage
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
    independentHistoricalExistenceCorroborationRecorded : Bool
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
  true false true true true true true true true true false

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data CandidateFilenameMeansExecutedInput : Set where
data ExistingArtifactMeansPublishedSameObject : Set where
data IndependentHistoricalUseMeansIbrahimInput : Set where
data MirrorDirectoryMeansExactArtifactHash : Set where
data ProducerDirectoryCommentMeansExactHash : Set where
data ChunkCountMeansRecoveredSplitLineage : Set where
data OctoberCandidateCancelsNovemberPublicationDescription : Set where

candidateFilenameDoesNotMeanExecutedInput : CandidateFilenameMeansExecutedInput → ⊥
candidateFilenameDoesNotMeanExecutedInput ()

artifactExistenceDoesNotMeanPublishedSameObject : ExistingArtifactMeansPublishedSameObject → ⊥
artifactExistenceDoesNotMeanPublishedSameObject ()

independentHistoricalUseDoesNotMeanIbrahimInput : IndependentHistoricalUseMeansIbrahimInput → ⊥
independentHistoricalUseDoesNotMeanIbrahimInput ()

mirrorDirectoryDoesNotMeanExactArtifactHash : MirrorDirectoryMeansExactArtifactHash → ⊥
mirrorDirectoryDoesNotMeanExactArtifactHash ()

producerDirectoryCommentDoesNotMeanExactHash : ProducerDirectoryCommentMeansExactHash → ⊥
producerDirectoryCommentDoesNotMeanExactHash ()

chunkCountDoesNotRecoverSplitLineage : ChunkCountMeansRecoveredSplitLineage → ⊥
chunkCountDoesNotRecoverSplitLineage ()

octoberCandidateDoesNotEraseNovemberDescription : OctoberCandidateCancelsNovemberPublicationDescription → ⊥
octoberCandidateDoesNotEraseNovemberPublicationDescription = octoberCandidateDoesNotEraseNovemberDescription

octoberCandidateDoesNotEraseNovemberDescription : OctoberCandidateCancelsNovemberPublicationDescription → ⊥
octoberCandidateDoesNotEraseNovemberDescription ()

remainingHistoricalPayment : String
remainingHistoricalPayment =
  "independent historical sources now corroborate the enwiki/20141008 directory and enwiki-20141008-pages-articles.xml.bz2 artifact name/existence, but the decisive same-object chain remains unpaid: acquire an authoritative copy or manifest and hash; recover or reconstruct the exact dump-to-112-small*.xml split lineage; execute the pinned parser/constructor equivalently; compare the reproduced FLN against the author-hosted fln.json/result object. Until then 2014-10-08 is the strongest concrete input candidate, not a promoted published-runtime identity."
