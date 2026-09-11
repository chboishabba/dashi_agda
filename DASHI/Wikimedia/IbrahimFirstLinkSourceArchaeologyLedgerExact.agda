module DASHI.Wikimedia.IbrahimFirstLinkSourceArchaeologyLedgerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- IBRAHIM FIRST-LINK SOURCE ARCHAEOLOGY LEDGER
--
-- Navigation/provenance owner only.  Mathematical/network claims remain owned
-- by WikipediaFirstLinkNetworkExact and DashiKnowledgeTraversalFunnelExact.
-- This ledger names the historical source manifestations and the current
-- consumer snapshot so they cannot be silently collapsed.
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
  "Primary preprint manifestation of the first-link-network method and reported 4.7M-article snapshot. It does not identify any 2026 Wikipedia edge."

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
  "A dated author-hosted manuscript carrier. Title/author lineage is compatible with the arXiv and journal objects; exact byte identity across manifestations is not inferred."

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
  "Version-of-record publication carrier for the method, traversal-funnel measure and reported historical first-link-network findings. DOI identity does not make current Wikipedia edges historical Ibrahim edges."

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
  "Provides primary routes to the 505 MB FLN map, traversal-visit/path-length/funnel JSONs and producer code. Hosting does not prove identity with every later mirror or regenerated dataset."

currentEnglishSnapshot : IbrahimSourceManifestation
currentEnglishSnapshot = ibrahim-source-manifestation
  currentWikipediaConsumerSnapshot
  "DASHI current-English audit"
  "Current English Wikipedia first-qualifying-link probes"
  "2026-09-10/11 audit tranche"
  "live English Wikipedia pages + Wikidata QIDs"
  "current empirical consumer snapshot"
  "000 Computer science, information & general works / domain-specific child Dewey coordinates downstream"
  "per-probe verified QIDs; unresolved values remain unresolved"
  "A new empirical consumer of the Ibrahim method. It is revision-sensitive and is not a manifestation of the 2016/2017 dataset."

------------------------------------------------------------------------
-- PRODUCER-REPOSITORY INPUT ARCHAEOLOGY
--
-- The author's repository itself currently carries two incompatible date cues
-- for the source English-Wikipedia dump.  code/readme.md says an
-- `enwiki2015--.xml` dump; first_link_txt.py comments point to the concrete
-- Wikimedia dump URL enwiki/20141008/.  Neither cue is silently preferred.
-- The parser code, however, does pay the extraction policy actually encoded in
-- that artifact: ignore links inside templates, parentheses, ref/div tags and
-- non-article namespaces; then return the first qualifying outermost wikilink.
------------------------------------------------------------------------

record HistoricalInputArchaeology : Set where
  constructor historical-input-archaeology
  field
    producerRepository : String
    readmeDumpCue : String
    parserDumpCue : String
    exactHistoricalDumpDateReconciled : Bool
    parserPolicyRecovered : Bool
    parserPolicy : String
    fullHistoricalFLNAvailable : Bool
    historicalEdgeIdentityPaidForCurrentProbes : Bool
    nextDiscriminator : String

open HistoricalInputArchaeology public

canonicalHistoricalInputArchaeology : HistoricalInputArchaeology
canonicalHistoricalInputArchaeology = historical-input-archaeology
  "marksibrahim/wikipedia_network"
  "code/readme.md: enwiki2015--.xml (date truncated/underspecified)"
  "code/first_link_txt.py: https://dumps.wikimedia.org/enwiki/20141008/"
  false
  true
  "parse article body; ignore templates, parentheses, <ref>, <div>, nested/non-article namespace links; return first qualifying outermost [[wikilink]] destination"
  true
  false
  "reconcile dump revision from paper/writeup/repository history or inspect the author-hosted FLN artifact metadata; only then compare targeted historical edges with the 2026 probes"

------------------------------------------------------------------------
-- Semantic-coordinate payments recovered by the current audit.
------------------------------------------------------------------------

record IbrahimSemanticCoordinatePayment : Set where
  constructor ibrahim-semantic-coordinate-payment
  field
    label : String
    qid : String
    qidVerified : Bool
    deweyTraversalOnly : Bool
    createsDashiDependency : Bool

open IbrahimSemanticCoordinatePayment public

individualCoordinate : IbrahimSemanticCoordinatePayment
individualCoordinate = ibrahim-semantic-coordinate-payment
  "individual" "Q795052" true true false

branchOfScienceCoordinate : IbrahimSemanticCoordinatePayment
branchOfScienceCoordinate = ibrahim-semantic-coordinate-payment
  "branch of science" "Q2465832" true true false

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
    readmeDumpCueOverridesParserDumpCue : Bool
    parserDumpCueOverridesReadmeDumpCue : Bool
    sourceManifestationsMayGuideHistoricalRecovery : Bool

open IbrahimSourceArchaeologyBoundary public

canonicalIbrahimSourceArchaeologyBoundary : IbrahimSourceArchaeologyBoundary
canonicalIbrahimSourceArchaeologyBoundary = ibrahim-source-archaeology-boundary
  false false false false false false false false false true
