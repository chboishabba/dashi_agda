module DASHI.Wikimedia.IbrahimFirstLinkNovember06ProducerPathStrengtheningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.IbrahimFirstLinkHistoricalDumpCandidateStrengtheningExact as Prior
import DASHI.Wikimedia.IbrahimFirstLinkHistoricalSnapshotProvenanceResidualExact as Historical

------------------------------------------------------------------------
-- THIN ARCHAEOLOGY DELTA: NOVEMBER 6 PRODUCER-PATH CANDIDATE
--
-- The earlier strongest concrete candidate was 2014-10-08 because the public
-- parser source comments explicitly name enwiki/20141008 and independent 2014
-- sources corroborate that dump's existence.
--
-- Deeper producer archaeology changes the ranking without silently deleting the
-- October cue:
--   * the paper methods source says the analysed raw snapshot is November 2014,
--     11M raw entries / 4.7M unique articles, distributed over 112 UVM cores;
--   * the producer preprocessing sources repeatedly name
--       /Volumes/mark external/wikipedia/enwiki_20141106.xml
--     as the original-file path;
--   * the chopping/preprocessing owner constructs exactly 112 small*.xml names;
--   * the author-hosted data appendix exposes the published FLN result as
--       data/fln.json (505 MB).
--
-- Therefore 2014-11-06 is now the strongest producer-path DATE candidate.
-- Exact dump-file variant/hash, raw split command, chunk hashes and reproduced
-- FLN same-object equality remain unpaid.
------------------------------------------------------------------------

priorBoundary : Prior.CandidateStrengtheningBoundary
priorBoundary = Prior.canonicalCandidateStrengtheningBoundary

historicalBoundary : Historical.HistoricalSnapshotProvenanceBoundary
historicalBoundary = Historical.canonicalHistoricalSnapshotProvenanceBoundary

------------------------------------------------------------------------
-- Source receipts.
------------------------------------------------------------------------

methodsSource : Attribution.AttributedSource
methodsSource = Attribution.mkNoDOISource
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds"
  "wikipedia-network.methods.tex"
  "marksibrahim/wikipedia_network; blob eae0d78df09ca838fd292d1a7d647ad737ee3789"
  "2016"
  "https://github.com/marksibrahim/wikipedia_network/blob/master/writeup/2016-04wikipedia-network/wikipedia-network.methods.tex"
  (Attribution.namedSourceKind "author research-methods source")
  "states November-2014 raw Wikipedia snapshot, 11 million raw articles/entries, 4.7 million unique articles, and distribution across 112 UVM cluster cores; month/scale/core-count evidence, not exact compressed artifact hash"
  Attribution.publicAttribution

processXmlV3Source : Attribution.AttributedSource
processXmlV3Source = Attribution.mkNoDOISource
  "Mark Ibrahim"
  "code/old_code/process/process_xml_v3.py"
  "marksibrahim/wikipedia_network; blob d6c5f939234e0160f0244f3396cb1c552d5bc6aa"
  "2015"
  "https://github.com/marksibrahim/wikipedia_network/blob/master/code/old_code/process/process_xml_v3.py"
  (Attribution.namedSourceKind "producer preprocessing source code")
  "repeatedly carries the commented original-file path /Volumes/mark external/wikipedia/enwiki_20141106.xml and later consumes the 112 small*.xml files; strong producer-path date cue, not proof of exact Wikimedia compressed variant or executed input hash"
  Attribution.publicAttribution

chopSource : Attribution.AttributedSource
chopSource = Attribution.mkNoDOISource
  "Mark Ibrahim"
  "code/old_code/process/chop_wiki.py"
  "marksibrahim/wikipedia_network; blob bbbf7667e430e7d520535ae2c88f528960884aaa"
  "2015"
  "https://github.com/marksibrahim/wikipedia_network/blob/master/code/old_code/process/chop_wiki.py"
  (Attribution.namedSourceKind "producer chunk-boundary repair source code")
  "constructs 104 small[a-d][a-z] names plus smallea-smalleh = 112 local chunks and repairs XML page boundaries; does not itself reveal the upstream raw split command"
  Attribution.publicAttribution

chopNotebookSource : Attribution.AttributedSource
chopNotebookSource = Attribution.mkNoDOISource
  "Mark Ibrahim"
  "code/old_code/process/chop_wiki.ipynb"
  "marksibrahim/wikipedia_network; blob b73063a341d56003fe53d466b1b213d95c7d94c1"
  "2015"
  "https://github.com/marksibrahim/wikipedia_network/blob/master/code/old_code/process/chop_wiki.ipynb"
  (Attribution.namedSourceKind "producer execution notebook")
  "contains the same 112-name boundary-repair loop and a recorded final IndexError from file_num+1 at the list boundary; execution defect retained rather than normalized away"
  Attribution.publicAttribution

authorDataPageSource : Attribution.AttributedSource
authorDataPageSource = Attribution.mkNoDOISource
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds / Computational Story Lab"
  "First Link Network data page"
  "Computational Story Lab online appendix"
  "2017"
  "https://compstorylab.org/share/papers/ibrahim2016a/data.html"
  Attribution.institutionalSource
  "author-hosted appendix identifies the First Link Network map as a 505 MB JSON result and links data/fln.json plus an XML-dump download surface; published result identity/availability, not exact dump-to-result lineage"
  Attribution.publicAttribution

wikimedia20141106IndependentSource : Attribution.AttributedSource
wikimedia20141106IndependentSource = Attribution.mkNoDOISource
  "Wikimedia XML dumps mailing-list participants / Wikimedia infrastructure records"
  "Independent 2014-11-06 dump existence receipts"
  "Wikimedia dumps ecosystem"
  "2015/2016"
  "https://lists.wikimedia.org/hyperkitty/list/xmldatadumps-l@lists.wikimedia.org/"
  (Attribution.namedSourceKind "independent technical provenance corroboration")
  "independent sources name the 2014-11-06 English Wikipedia pages-articles family; Wikimedia Phabricator later records a decompressed enwiki-20141106-pages-articles.xml copy. Confirms date/family existence only, not Ibrahim same-object use"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Candidate ranking.
------------------------------------------------------------------------

data RuntimeDateCandidate : Set where
  october08ParserCommentCandidate : RuntimeDateCandidate
  november06ProducerPathCandidate : RuntimeDateCandidate

record ProducerPathCandidateReceipt : Set where
  constructor producer-path-candidate-receipt
  field
    strongestDateCandidate : RuntimeDateCandidate
    paperMonthMatchesCandidateMonth : Bool
    authorBlogMonthMatchesCandidateMonth : Bool
    producerOriginalPathNames20141106 : Bool
    producerUses112ChunkNamespace : Bool
    methodsSay112Cores : Bool
    independent20141106DumpFamilyExistencePaid : Bool
    authorPublishedFlnJsonIdentityPaid : Bool
    exactCompressedVariantPaid : Bool
    exactArtifactHashPaid : Bool
    exactRawSplitCommandPaid : Bool
    exactChunkHashesPaid : Bool
    chopNotebookRecordedIndexErrorRetained : Bool
    parserEquivalentExecutionPaid : Bool
    reproducedFlnEqualsPublishedFlnPaid : Bool
    octoberParserCommentRetained : Bool
open ProducerPathCandidateReceipt public

strongestProducerPathCandidate : ProducerPathCandidateReceipt
strongestProducerPathCandidate = producer-path-candidate-receipt
  november06ProducerPathCandidate
  true true true true true true true
  false false false false true false false true

------------------------------------------------------------------------
-- October remains a source cue but no longer outranks the producer path.
------------------------------------------------------------------------

data ParserCommentDeterminesRuntime : Set where
data ProducerPathDateDeterminesExactArtifact : Set where
data SameMonthMeansSameDump : Set where
data CoreCountDeterminesChunkLineage : Set where
data PublishedFlnUrlDeterminesInputDump : Set where
data RecordedNotebookErrorMayBeIgnored : Set where

octoberParserCommentDoesNotDetermineRuntime : ParserCommentDeterminesRuntime → ⊥
octoberParserCommentDoesNotDetermineRuntime ()

producerDateDoesNotDetermineExactArtifact : ProducerPathDateDeterminesExactArtifact → ⊥
producerDateDoesNotDetermineExactArtifact ()

sameMonthDoesNotMeanSameDump : SameMonthMeansSameDump → ⊥
sameMonthDoesNotMeanSameDump ()

coreCountDoesNotDetermineChunkLineage : CoreCountDeterminesChunkLineage → ⊥
coreCountDoesNotDetermineChunkLineage ()

publishedFlnUrlDoesNotDetermineInputDump : PublishedFlnUrlDeterminesInputDump → ⊥
publishedFlnUrlDoesNotDetermineInputDump ()

recordedNotebookErrorMustRemainVisible : RecordedNotebookErrorMayBeIgnored → ⊥
recordedNotebookErrorMustRemainVisible ()

------------------------------------------------------------------------
-- Revised remaining payment.
------------------------------------------------------------------------

remainingNovember06Payment : String
remainingNovember06Payment =
  "2014-11-06 is now the strongest producer-path date candidate because the publication methods say November 2014/112 cores, producer preprocessing repeatedly names enwiki_20141106.xml, and the chunk-preparation code enumerates 112 small*.xml names. Remaining same-object debt: identify the exact Wikimedia 20141106 pages-articles variant actually decompressed/renamed as enwiki_20141106.xml; recover authoritative manifest/hash or historical bytes; recover the raw dump-to-112 pre-split command and chunk hashes (the surviving chop script only repairs page boundaries and its notebook records a terminal IndexError); execute parser/constructor equivalently; and hash/compare the result against author-hosted data/fln.json. The 20141008 parser comment remains an append-only stale/conflicting cue, not the leading runtime candidate."

record November06StrengtheningBoundary : Set where
  constructor november06-strengthening-boundary
  field
    november06IsStrongestProducerDateCandidate : Bool
    november06IsExactExecutedArtifactIdentity : Bool
    october08CueRetained : Bool
    publicationNovemberCueRetained : Bool
    methods112CoreReceiptRetained : Bool
    producer112ChunkReceiptRetained : Bool
    authorFlnResultIdentityRetained : Bool
    exactArtifactHashStillRequired : Bool
    rawSplitLineageStillRequired : Bool
    parserEquivalentReproductionStillRequired : Bool
    publishedResultSameObjectStillRequired : Bool
    recordedProducerErrorRetained : Bool
open November06StrengtheningBoundary public

canonicalNovember06StrengtheningBoundary : November06StrengtheningBoundary
canonicalNovember06StrengtheningBoundary = november06-strengthening-boundary
  true false true true true true true true true true true true
