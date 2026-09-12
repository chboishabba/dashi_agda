module DASHI.Wikimedia.IbrahimFirstLinkProducerRevisionArchaeologyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimFirstLinkPrimarySourceDeweyQidDoiBidiExact as Primary
import DASHI.Wikimedia.WikipediaFirstLinkNetworkExact as FLN

------------------------------------------------------------------------
-- IBRAHIM FIRST-LINK PRODUCER REVISION ARCHAEOLOGY
--
-- Snowball rule: paper, producer code, released data and later code revisions
-- are separate carriers. Acquisition may find them in any order, but a later
-- artifact may not silently rewrite the historical runtime identity.
------------------------------------------------------------------------

record ProducerArtifact : Set where
  constructor producer-artifact
  field
    owner : String
    artifact : String
    stableId : String
    canonicalLink : String
    sourceRole : String
    boundedReading : String
    excludedPromotion : String
    claimOwner : String
open ProducerArtifact public

paperCarrier : ProducerArtifact
paperCarrier = producer-artifact
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds"
  "Connecting every bit of knowledge: The structure of Wikipedia's First Link Network"
  "DOI 10.1016/j.jocs.2016.12.001; arXiv:1605.00309"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  "peer-reviewed primary scientific source"
  "English Wikipedia FLN described as November 2014; construction and traversal-funnel interpretation"
  "does not by itself identify exact dump day/file, exact producer revision or later code semantics"
  "externalSourceOwner"

producerRepository : ProducerArtifact
producerRepository = producer-artifact
  "Mark Ibrahim / marksibrahim"
  "marksibrahim/wikipedia_network"
  "GitHub repository id 43619217"
  "https://github.com/marksibrahim/wikipedia_network"
  "first-party producer code and research-material repository"
  "contains extraction/parser pipeline, analysis code, writeup history and online-appendix linkage"
  "repository identity does not prove which revision generated a particular released result"
  "externalProducerOwner"

initialProducerCommit : ProducerArtifact
initialProducerCommit = producer-artifact
  "Mark Ibrahim"
  "initial public wikipedia_network commit"
  "git 9dd11de2676860751b02c1bbb0aeee0afb7b2710"
  "https://github.com/marksibrahim/wikipedia_network/commit/9dd11de2676860751b02c1bbb0aeee0afb7b2710"
  "producer-code chronology receipt"
  "initial public commit on 2015-10-04; contains parser/extraction code and November-2014 filename cues"
  "public commit date is not original execution date and does not establish exact runtime checkout"
  "externalProducerOwner"

releasedFlnMap : ProducerArtifact
releasedFlnMap = producer-artifact
  "Computational Story Lab / Ibrahim-Danforth-Dodds"
  "First Link Network Map (article -> first link)"
  "online appendix data/fln.json; advertised size 505 MB"
  "https://compstorylab.org/share/papers/ibrahim2016a/data/fln.json"
  "first-party released result data"
  "released article-to-first-link graph output associated with the paper"
  "released output does not by itself identify exact input dump or prove parser-equivalent regeneration"
  "externalProducerOwner"

------------------------------------------------------------------------
-- Competing dump cues.
------------------------------------------------------------------------

record DumpCue : Set where
  constructor dump-cue
  field
    cue : String
    carrier : String
    strength : String
    agreesWithPaperMonth : Bool
    exactRuntimeIdentityPaid : Bool
open DumpCue public

octoberEightCue : DumpCue
octoberEightCue = dump-cue
  "https://dumps.wikimedia.org/enwiki/20141008/"
  "code/first_link_txt.py comment"
  "first-party parser code cue"
  false
  false

novemberSixCue : DumpCue
novemberSixCue = dump-cue
  "/Volumes/mark external/wikipedia/enwiki_20141106.xml"
  "old_code/process/process_xml*.py/ipynb producer workflow"
  "first-party full-input filename repeated across XML-processing artifacts"
  true
  false

novemberSixArchiveObject : String
novemberSixArchiveObject =
  "Wikimedia enwiki/20141106 snapshot; contemporary dump-list discussion names enwiki-20141106-pages-articles-multistream.xml.bz2 (~11.3 GB)"

strongestCurrentDumpCandidate : String
strongestCurrentDumpCandidate =
  "2014-11-06 / enwiki_20141106.xml: strongest current runtime candidate because producer XML-processing workflow names it and it agrees with paper/blog November-2014 statement; exact ancestry into producer chunks remains unpaid"

------------------------------------------------------------------------
-- Parser semantics paid directly by first-party producer code.
------------------------------------------------------------------------

record ParserSemanticsReceipt : Set where
  constructor parser-semantics-receipt
  field
    excludesTemplates : Bool
    excludesParentheses : Bool
    excludesRefTags : Bool
    excludesDivTags : Bool
    rejectsNonArticleNamespaces : Bool
    returnsDestinationNotDisplayText : Bool
    firstQualifyingOuterLink : Bool
    exactHistoricalRuntimeRevisionPaid : Bool
open ParserSemanticsReceipt public

producerParserSemantics : ParserSemanticsReceipt
producerParserSemantics = parser-semantics-receipt
  true true true true true true true false

parserBlobAtCurrentMaster : String
parserBlobAtCurrentMaster = "code/first_link_txt.py blob a830c47905d4cde90876e1097f2620f4f19a63df"

------------------------------------------------------------------------
-- Producer transformation chain.
------------------------------------------------------------------------

record ProducerTransformation : Set where
  constructor producer-transformation
  field
    upstream : String
    downstream : String
    producerReceipt : String
    paid : Bool
open ProducerTransformation public

novemberDumpToCleanSmall : ProducerTransformation
novemberDumpToCleanSmall = producer-transformation
  "enwiki_20141106.xml candidate full input"
  "clean_small/*"
  "no source-paid split/decompression command located in current repository archaeology"
  false

cleanSmallToFullWikiData : ProducerTransformation
cleanSmallToFullWikiData = producer-transformation
  "clean_small/small*"
  "/users/m/s/msibrahi/full_wiki_data/small*.xml"
  "old_code/process/chop_wiki.py repairs chunk boundaries at </page>, carries paths from external clean_small to cluster full_wiki_data, and renames chunks to .xml"
  true

fullWikiDataToChunkJson : ProducerTransformation
fullWikiDataToChunkJson = producer-transformation
  "/users/m/s/msibrahi/full_wiki_data/small*.xml"
  "v4/results/true_flnetwork/<chunk>.json"
  "code/create_fln.py enumerates 112 small*.xml inputs and applies first_link_txt.run_parser"
  true

chunkJsonToFln : ProducerTransformation
chunkJsonToFln = producer-transformation
  "112 per-chunk first-link JSON objects"
  "combined fln.json"
  "code/combine_fln.py merges 112 dictionaries; official appendix exposes FLN data/fln.json"
  true

producerSplitShape : String
producerSplitShape =
  "clean_small -> full_wiki_data/small*.xml -> 112 chunk JSON outputs -> combined fln.json"

------------------------------------------------------------------------
-- Traversal-funnel algorithm has its own revision lineage.
------------------------------------------------------------------------

record AlgorithmRevision : Set where
  constructor algorithm-revision
  field
    revision : String
    date : String
    role : String
    cycleStartIncrementExplicit : Bool
    paperEra : Bool
open AlgorithmRevision public

paperEraTraversalPseudo : AlgorithmRevision
paperEraTraversalPseudo = algorithm-revision
  "ce2f02562e71de2697051313201a761ae0266b56 -> 59433702a975c9b3a562b1027a2d5f43bb3a7150"
  "2016-11-18 -> 2016-11-21"
  "reviewer-requested traversal-funnel pseudocode added to paper/writeup lineage"
  false
  true

laterTraversalCorrection : AlgorithmRevision
laterTraversalCorrection = algorithm-revision
  "cd3b71d1e176cc1a9ebcd8542b48245dc900b458"
  "2019-08-25"
  "later public pseudocode correction: explicitly increment start of a cycle"
  true
  false

------------------------------------------------------------------------
-- Current reproduction cutset.
------------------------------------------------------------------------

record ProducerReproductionState : Set where
  constructor producer-reproduction-state
  field
    primaryPaperPaid : Bool
    firstPartyProducerRepoPaid : Bool
    releasedFlnMapPaid : Bool
    parserSemanticsPaid : Bool
    novemberSixCandidatePaidAsCandidate : Bool
    cleanSmallToReleasedFlnLineagePaid : Bool
    exactInputDumpIdentityPaid : Bool
    dumpToCleanSmallAncestryPaid : Bool
    exactExtractionRevisionPaid : Bool
    exactPaperEraFunnelRevisionPaid : Bool
    releasedFlnRegeneratedByteEquivalent : Bool
    traversalProductsRegeneratedEquivalent : Bool
open ProducerReproductionState public

currentProducerReproductionState : ProducerReproductionState
currentProducerReproductionState = producer-reproduction-state
  true true true true true true false false false false false false

firstUnpaidProducerJoin : String
firstUnpaidProducerJoin =
  "same-object ancestry: enwiki_20141106.xml (or other exact Wikimedia dump object) -> clean_small split used by the producer pipeline"

secondUnpaidProducerJoin : String
secondUnpaidProducerJoin =
  "identify exact extraction-code revision that generated released 505 MB fln.json, then distinguish paper-era traversal-funnel semantics from 2019 cycle-start correction"

------------------------------------------------------------------------
-- External navigation remains inherited from primary source ledger.
------------------------------------------------------------------------

wikipediaQid : String
wikipediaQid = "Q52"

graphTheoryQid : String
graphTheoryQid = "Q131476"

directedGraphQid : String
directedGraphQid = "Q1137726"

networkScienceQid : String
networkScienceQid = "Q2434424"

graphTheoryDewey : String
graphTheoryDewey = "511.5"

directedGraphDewey : String
directedGraphDewey = "511.54"

producerRepoQid : String
producerRepoQid = "unresolved/not required: GitHub repository identity is carried by repository id + git objects"

producerRepoDewey : String
producerRepoDewey = "not promoted: library classification does not identify a producer revision"

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data OctoberCodeCueMeansRuntime : Set where
data NovemberFilenameMeansExactRuntime : Set where
data ReleasedDataMeansReproduced : Set where
data CurrentRepoMeansPaperCode : Set where
data LaterFunnelFixMeansHistoricalResultUsedFix : Set where
data DownstreamChunkLineageMeansUpstreamDumpAncestry : Set where

octoberCueDoesNotFixRuntime : OctoberCodeCueMeansRuntime → ⊥
octoberCueDoesNotFixRuntime ()

novemberFilenameDoesNotProveRuntime : NovemberFilenameMeansExactRuntime → ⊥
novemberFilenameDoesNotProveRuntime ()

releasedDataDoesNotProveReproduction : ReleasedDataMeansReproduced → ⊥
releasedDataDoesNotProveReproduction ()

currentRepoDoesNotEqualPaperCode : CurrentRepoMeansPaperCode → ⊥
currentRepoDoesNotEqualPaperCode ()

laterFixDoesNotRewriteHistoricalRun : LaterFunnelFixMeansHistoricalResultUsedFix → ⊥
laterFixDoesNotRewriteHistoricalRun ()

downstreamLineageDoesNotCreateDumpAncestry : DownstreamChunkLineageMeansUpstreamDumpAncestry → ⊥
downstreamLineageDoesNotCreateDumpAncestry ()

primaryBoundary : Primary.FirstLinkDeweyQidDoiBoundary
primaryBoundary = Primary.canonicalFirstLinkDeweyQidDoiBoundary

flnBoundary : FLN.FirstLinkNetworkBoundary
flnBoundary = FLN.canonicalFirstLinkNetworkBoundary
