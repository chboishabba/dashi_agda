module DASHI.Wikimedia.IbrahimFirstLinkPrimarySourceDeweyQidDoiBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.ScientificReferenceEntityAtlasExact as Atlas

------------------------------------------------------------------------
-- IBRAHIM FIRST-LINK PRIMARY-SOURCE / DEWEY / QID / DOI BIDI LEDGER
--
-- Primary source:
-- Mark Ibrahim, Christopher M. Danforth, Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's First
-- Link Network", Journal of Computational Science 19 (2017), 21-30.
-- DOI 10.1016/j.jocs.2016.12.001; arXiv:1605.00309.
--
-- The paper constructs a directed first-link network from English Wikipedia
-- as of November 2014.  DOI identifies the scholarly source; QID identifies
-- present external concepts/entities; Dewey supplies library-navigation
-- coordinates.  None reconstructs the exact historical dump/parser state.
------------------------------------------------------------------------

ibrahimFirstLinkPaper : Attribution.AttributedSource
ibrahimFirstLinkPaper = Attribution.mkDOISource
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds"
  "Connecting every bit of knowledge: The structure of Wikipedia's First Link Network"
  "Journal of Computational Science 19, 21-30"
  "2017"
  "10.1016/j.jocs.2016.12.001"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  Attribution.academicArticleSource
  "primary scientific owner for the English-Wikipedia First Link Network construction, traversal statistics and traversal-funnel method; paper states the network uses English Wikipedia as of November 2014"
  Attribution.publicAttribution

arxivCoordinate : String
arxivCoordinate = "arXiv:1605.00309"

historicalCorpusMonth : String
historicalCorpusMonth = "English Wikipedia as of November 2014"

exactHistoricalDumpDay : String
exactHistoricalDumpDay = "unresolved: month paid by paper; exact dump day/file not promoted"

------------------------------------------------------------------------
-- QID coordinates.  Reuse the existing scientific-reference entity layer.
------------------------------------------------------------------------

wikipediaEntity : Atlas.ScientificReferenceEntity
wikipediaEntity = Atlas.verified "Wikipedia" Atlas.conceptEntity "Q52"
  "Wikidata identity inspected 2026-09-11; present entity identity only"

graphTheoryEntity : Atlas.ScientificReferenceEntity
graphTheoryEntity = Atlas.verified "graph theory" Atlas.conceptEntity "Q131476"
  "Wikidata identity inspected 2026-09-11"

directedGraphEntity : Atlas.ScientificReferenceEntity
directedGraphEntity = Atlas.verified "directed graph" Atlas.conceptEntity "Q1137726"
  "Wikidata identity inspected 2026-09-11"

networkScienceEntity : Atlas.ScientificReferenceEntity
networkScienceEntity = Atlas.verified "network science" Atlas.conceptEntity "Q2434424"
  "Wikidata identity inspected 2026-09-11"

philosophyEntity : Atlas.ScientificReferenceEntity
philosophyEntity = Atlas.verified "philosophy" Atlas.conceptEntity "Q5891"
  "Wikidata identity inspected 2026-09-11"

------------------------------------------------------------------------
-- Dewey coordinates.  Only exact inspected DDC values are promoted.
------------------------------------------------------------------------

record DeweyCoordinate : Set where
  constructor dewey-coordinate
  field
    subject : String
    number : String
    source : String
    resolved : Bool
open DeweyCoordinate public

graphTheoryDewey : DeweyCoordinate
graphTheoryDewey = dewey-coordinate
  "graph theory" "511.5"
  "Wikidata Q131476 DDC statement inspected 2026-09-11" true

directedGraphDewey : DeweyCoordinate
directedGraphDewey = dewey-coordinate
  "directed graph" "511.54"
  "Wikidata Q1137726 DDC statement inspected 2026-09-11" true

philosophyDewey : DeweyCoordinate
philosophyDewey = dewey-coordinate
  "philosophy" "100"
  "Wikidata Q5891 DDC statement inspected 2026-09-11" true

networkScienceDewey : DeweyCoordinate
networkScienceDewey = dewey-coordinate
  "network science" "unresolved"
  "Q2434424 identity paid; no exact inspected DDC promoted in this pass" false

wikipediaDewey : DeweyCoordinate
wikipediaDewey = dewey-coordinate
  "Wikipedia" "unresolved"
  "Q52 identity paid; no exact inspected DDC promoted in this pass" false

traversalFunnelDewey : DeweyCoordinate
traversalFunnelDewey = dewey-coordinate
  "Ibrahim traversal funnel" "not-applicable/unresolved"
  "paper-specific analytic construct; do not manufacture a library class from graph/network neighbours" false

------------------------------------------------------------------------
-- Source-paid readings versus still-open historical reproduction.
------------------------------------------------------------------------

record FirstLinkPrimarySourceReceipt : Set where
  constructor first-link-primary-source-receipt
  field
    journalDoiPaid : Bool
    arxivIdentityPaid : Bool
    november2014CorpusMonthPaid : Bool
    directedNetworkConstructionPaid : Bool
    traversalFunnelMethodPaid : Bool
    exactDumpDayPaid : Bool
    exactDumpFilePaid : Bool
    parserEquivalentReproductionPaid : Bool
    currentWikipediaEdgesEqualHistoricalEdges : Bool
open FirstLinkPrimarySourceReceipt public

canonicalFirstLinkPrimarySourceReceipt : FirstLinkPrimarySourceReceipt
canonicalFirstLinkPrimarySourceReceipt = first-link-primary-source-receipt
  true true true true true false false false false

------------------------------------------------------------------------
-- WrongType / no-promotion gates.
------------------------------------------------------------------------

data DoiCreatesHistoricalCorpus : Set where
data QidCreatesHistoricalFirstLink : Set where
data DeweyCreatesSemanticEdge : Set where
data CurrentWikipediaCreates2014Edge : Set where
data DirectedGraphClassCreatesTraversalFunnel : Set where

doiDoesNotCreateHistoricalCorpus : DoiCreatesHistoricalCorpus → ⊥
doiDoesNotCreateHistoricalCorpus ()

qidDoesNotCreateHistoricalFirstLink : QidCreatesHistoricalFirstLink → ⊥
qidDoesNotCreateHistoricalFirstLink ()

deweyDoesNotCreateSemanticEdge : DeweyCreatesSemanticEdge → ⊥
deweyDoesNotCreateSemanticEdge ()

currentWikipediaDoesNotCreate2014Edge : CurrentWikipediaCreates2014Edge → ⊥
currentWikipediaDoesNotCreate2014Edge ()

directedGraphClassDoesNotCreateTraversalFunnel : DirectedGraphClassCreatesTraversalFunnel → ⊥
directedGraphClassDoesNotCreateTraversalFunnel ()

------------------------------------------------------------------------
-- BIDI interpretation.
--
-- Forward: historical FLN source -> directed-graph/network-science navigation.
-- Reverse: graph/QID/DDC coordinates may help discovery but may not pay the
-- historical first-link edge, dump identity, or parser-equivalent replay.
------------------------------------------------------------------------

record FirstLinkDeweyQidDoiBoundary : Set where
  constructor first-link-dewey-qid-doi-boundary
  field
    doiTravelsAsSourceIdentity : Bool
    qidTravelsAsPresentEntityIdentity : Bool
    deweyTravelsAsLibraryNavigation : Bool
    paperOwnsHistoricalMethodReading : Bool
    unresolvedDeweyRetained : Bool
    historicalDumpIdentityStillSeparate : Bool
    historicalParserReplayStillSeparate : Bool
    presentEntityIdentityCreatesHistoricalEdge : Bool
    classificationCreatesHistoricalEdge : Bool
open FirstLinkDeweyQidDoiBoundary public

canonicalFirstLinkDeweyQidDoiBoundary : FirstLinkDeweyQidDoiBoundary
canonicalFirstLinkDeweyQidDoiBoundary = first-link-dewey-qid-doi-boundary
  true true true true true true true false false
