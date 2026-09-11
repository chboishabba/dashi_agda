module DASHI.Wikimedia.IbrahimFirstLinkSourceArchaeologyLedgerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- IBRAHIM FIRST-LINK SOURCE ARCHAEOLOGY LEDGER
--
-- Navigation/provenance owner only. Mathematical/network claims remain owned
-- by WikipediaFirstLinkNetworkExact and DashiKnowledgeTraversalFunnelExact.
------------------------------------------------------------------------

data IbrahimSourceRole : Set where
  methodPreprint methodAuthorDraft methodJournalVersion
  authorHostedCodeData currentWikipediaConsumerSnapshot : IbrahimSourceRole

record IbrahimSourceManifestation : Set where
  constructor ibrahim-source-manifestation
  field
    role : IbrahimSourceRole
    authors : String
    title : String
    dateOrVersion : String
    stableIdentifier : String
    sourceClass : String
    deweyTraversal : String
    primaryQidCoordinates : String
    boundedReading : String

open IbrahimSourceManifestation public

arxiv160500309 : IbrahimSourceManifestation
arxiv160500309 = ibrahim-source-manifestation
  methodPreprint
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds"
  "Connecting every bit of knowledge: The structure of Wikipedia's First Link Network"
  "submitted 2016-05-01"
  "arXiv:1605.00309"
  "primary author preprint manifestation"
  "004 Computer science / data processing"
  "Mark Ibrahim unresolvedQid; Christopher M. Danforth Q89437200; Peter Sheridan Dodds Q42772652"
  "Primary preprint manifestation of the method and reported historical network; not a carrier for any 2026 Wikipedia edge."

authorDraft20161120 : IbrahimSourceManifestation
authorDraft20161120 = ibrahim-source-manifestation
  methodAuthorDraft
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds"
  "Connecting every bit of knowledge: The structure of Wikipedia's First Link Network"
  "author-hosted draft dated 2016-11-20"
  "Computational Story Lab author-hosted PDF"
  "primary author-hosted manuscript manifestation"
  "004 Computer science / data processing"
  "Mark Ibrahim unresolvedQid; Christopher M. Danforth Q89437200; Peter Sheridan Dodds Q42772652"
  "Title/author lineage is compatible with arXiv/journal manifestations; byte identity is not inferred."

journal2017 : IbrahimSourceManifestation
journal2017 = ibrahim-source-manifestation
  methodJournalVersion
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds"
  "Connecting every bit of knowledge: The structure of Wikipedia's First Link Network"
  "Journal of Computational Science 19 (2017), 21-30"
  "DOI 10.1016/j.jocs.2016.12.001"
  "primary peer-reviewed publication"
  "004 Computer science / data processing"
  "Mark Ibrahim unresolvedQid; Christopher M. Danforth Q89437200; Peter Sheridan Dodds Q42772652"
  "Version-of-record carrier for the method, traversal-funnel measure and reported historical findings; DOI identity does not identify a later Wikipedia snapshot."

storyLabCodeData : IbrahimSourceManifestation
storyLabCodeData = ibrahim-source-manifestation
  authorHostedCodeData
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds / Computational Story Lab"
  "Connecting Every Bit of Knowledge: Explore the paper"
  "author-hosted project page"
  "UVM Computational Story Lab paper/code/data page; github.com/marksibrahim/wikipedia_network"
  "primary author-hosted project/code/data surface"
  "004 Computer science / data processing"
  "Christopher M. Danforth Q89437200; Peter Sheridan Dodds Q42772652; Mark Ibrahim unresolvedQid"
  "Primary routes to the 505 MB FLN map, traversal results and producer code; hosting does not prove identity with later mirrors or regenerated datasets."

currentEnglishSnapshot : IbrahimSourceManifestation
currentEnglishSnapshot = ibrahim-source-manifestation
  currentWikipediaConsumerSnapshot
  "DASHI current-English audit"
  "Current English Wikipedia first-link probes"
  "2026-09-10/11 audit tranche"
  "live English Wikipedia pages + Wikidata QIDs"
  "current empirical consumer snapshot"
  "000 Computer science, information & general works / downstream domain coordinates"
  "per-probe verified QIDs; unresolved values remain unresolved"
  "A new empirical consumer of the Ibrahim method, not a manifestation of the historical dataset."

------------------------------------------------------------------------
-- PRODUCER-REPOSITORY INPUT ARCHAEOLOGY
------------------------------------------------------------------------

record HistoricalInputArchaeology : Set where
  constructor historical-input-archaeology
  field
    producerRepository : String
    readmeDumpCue : String
    parserDumpCue : String
    paperSnapshotCue : String
    storyLabBlogSnapshotCue : String
    parserCueReplicatedAcrossProducerArtifacts : Bool
    readme2015CueUniqueInFocusedSearch : Bool
    historicalRuntimeMonthPaid : Bool
    historicalRuntimeMonth : String
    exactRuntimeDumpDayPaid : Bool
    parserPolicyRecovered : Bool
    parserPolicy : String
    currentAuditPolicy : String
    currentAuditParserEquivalentPaid : Bool
    fullHistoricalFLNAvailable : Bool
    historicalEdgeIdentityPaidForAllCurrentProbes : Bool
    nextDiscriminator : String

open HistoricalInputArchaeology public

canonicalHistoricalInputArchaeology : HistoricalInputArchaeology
canonicalHistoricalInputArchaeology = historical-input-archaeology
  "marksibrahim/wikipedia_network"
  "code/readme.md: enwiki2015--.xml (date truncated/underspecified)"
  "code/first_link_txt.py and old parser/test copies: https://dumps.wikimedia.org/enwiki/20141008/"
  "author-hosted paper: English Wikipedia as of November 2014"
  "Computational Story Lab blog: snapshot of English Wikipedia in November 2014"
  true
  true
  true
  "2014-11"
  false
  true
  "parse page body; ignore templates, parentheses, <ref>, <div>, nested/non-article namespace links; return first qualifying outermost [[wikilink]] destination"
  "current DASHI audit uses hand-inspected first qualifying conceptual link after hatnote/disambiguation exclusions"
  false
  true
  false
  "recover exact November-2014 dump file/day and reproduce the original parser for the remaining targeted pages; compare only after those two same-object gates are paid"

------------------------------------------------------------------------
-- Historical edge receipts recovered directly from the primary writeup.
------------------------------------------------------------------------

data HistoricalEdgeComparisonStatus : Set where
  historicallyStable changed renamed unresolvedHistorical : HistoricalEdgeComparisonStatus

record HistoricalEdgeComparison : Set where
  constructor historical-edge-comparison
  field
    child : String
    historicalParent : String
    historicalSource : String
    historicalSnapshot : String
    currentParent : String
    currentObservationDate : String
    status : HistoricalEdgeComparisonStatus
    exactHistoricalEdgePaid : Bool
    currentEdgePaid : Bool
    boundedReading : String

open HistoricalEdgeComparison public

economicsHistoricalComparison : HistoricalEdgeComparison
economicsHistoricalComparison = historical-edge-comparison
  "Economics"
  "Social Science"
  "Ibrahim-Danforth-Dodds author-hosted paper, Figure 1 / Train path"
  "English Wikipedia November 2014 FLN"
  "social science"
  "2026-09-10"
  historicallyStable
  true
  true
  "The primary paper explicitly prints Economics -> Social Science in the historical FLN, and the current audit observes the same destination modulo title case. This pays stability for this edge only; it does not pay parser equivalence or the remaining current probes."

------------------------------------------------------------------------
-- Semantic-coordinate payments recovered by the current audit.
------------------------------------------------------------------------

record IbrahimSemanticCoordinatePayment : Set where
  constructor ibrahim-semantic-coordinate-payment
  field label : String; qid : String; qidVerified : Bool; deweyTraversalOnly : Bool; createsDashiDependency : Bool
open IbrahimSemanticCoordinatePayment public

individualCoordinate = ibrahim-semantic-coordinate-payment "individual" "Q795052" true true false
branchOfScienceCoordinate = ibrahim-semantic-coordinate-payment "branch of science" "Q2465832" true true false

------------------------------------------------------------------------
-- Archaeology firewalls.
------------------------------------------------------------------------

record IbrahimSourceArchaeologyBoundary : Set where
  constructor ibrahim-source-archaeology-boundary
  field
    arxivEqualsJournalBytes : Bool
    authorDraftEqualsJournalBytes : Bool
    doiIdentifiesCurrentWikipediaSnapshot : Bool
    currentSnapshotEqualsHistoricalIbrahimGraph : Bool
    qidCreatesHistoricalEdgeIdentity : Bool
    deweyCreatesSourceAuthority : Bool
    traversalFunnelRankCreatesEpistemicAuthority : Bool
    parserCommentDateOverridesPaperSnapshotMonth : Bool
    readme2015CueOverridesPaperSnapshotMonth : Bool
    historicalMonthDeterminesExactDumpDay : Bool
    onePaidHistoricalEdgePaysAllProbeEdges : Bool
    currentConceptualPolicyEqualsOriginalParser : Bool
    sourceManifestationsMayGuideHistoricalRecovery : Bool

open IbrahimSourceArchaeologyBoundary public

canonicalIbrahimSourceArchaeologyBoundary = ibrahim-source-archaeology-boundary
  false false false false false false false false false false false false true
