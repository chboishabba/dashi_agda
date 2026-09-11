module DASHI.Wikimedia.IbrahimFirstLinkProducerArchaeologyDeweyDoiQidExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution

------------------------------------------------------------------------
-- IBRAHIM FIRST-LINK PRODUCER ARCHAEOLOGY / DEWEY / DOI / QID SNOWBALL
--
-- Highest-alpha historical-reproduction residual for the Ibrahim FLN.
-- Separate the published claim, released parser, local production carrier,
-- derived FLN map, graph statistics, present external identities and library
-- classification coordinates.  Acquisition may snowball sideways; payment may
-- not skip an unresolved same-object producer join.
------------------------------------------------------------------------

ibrahimPaper : Attribution.AttributedSource
ibrahimPaper = Attribution.mkDOISource
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds"
  "Connecting every bit of knowledge: The structure of Wikipedia's First Link Network"
  "Journal of Computational Science 19, 21-30"
  "2017"
  "10.1016/j.jocs.2016.12.001"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  Attribution.academicArticleSource
  "primary scientific owner for the FLN construction, November-2014 corpus description, graph measurements and traversal-funnel analysis"
  Attribution.publicAttribution

releasedCode : Attribution.AttributedSource
releasedCode = Attribution.mkNoDOISource
  "Mark Ibrahim"
  "marksibrahim/wikipedia_network"
  "GitHub source repository linked by the authors' online appendix"
  "2015-2019 public history"
  "https://github.com/marksibrahim/wikipedia_network"
  Attribution.namedSourceKind
  "released implementation/source-history carrier; not by itself proof of the exact executed production revision or local input bytes"
  Attribution.publicAttribution

onlineAppendixData : Attribution.AttributedSource
onlineAppendixData = Attribution.mkNoDOISource
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds"
  "First Link Network online appendix data"
  "Computational Story Lab"
  "2017"
  "https://compstorylab.org/share/papers/ibrahim2016a/data.html"
  Attribution.institutionalSource
  "author-linked distribution surface for FLN map and derived traversal visits, indegree, path lengths, traversal funnels and cycles"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- External coordinates: identity/navigation only.
------------------------------------------------------------------------

record GraphCoordinate : Set where
  constructor graph-coordinate
  field
    label : String
    qid : String
    dewey : String
    link : String
    resolvedDewey : Bool
open GraphCoordinate public

wikipediaCoordinate : GraphCoordinate
wikipediaCoordinate = graph-coordinate
  "Wikipedia" "Q52" "unresolved"
  "https://www.wikidata.org/wiki/Q52" false

graphTheoryCoordinate : GraphCoordinate
graphTheoryCoordinate = graph-coordinate
  "graph theory" "Q131476" "511.5"
  "https://www.wikidata.org/wiki/Q131476" true

directedGraphCoordinate : GraphCoordinate
directedGraphCoordinate = graph-coordinate
  "directed graph" "Q1137726" "511.54"
  "https://www.wikidata.org/wiki/Q1137726" true

networkScienceCoordinate : GraphCoordinate
networkScienceCoordinate = graph-coordinate
  "network science" "Q2434424" "unresolved"
  "https://www.wikidata.org/wiki/Q2434424" false

philosophyCoordinate : GraphCoordinate
philosophyCoordinate = graph-coordinate
  "philosophy" "Q5891" "100"
  "https://www.wikidata.org/wiki/Q5891" true

paperQid : String
paperQid = "unresolved: no safely verified Wikidata scholarly-article item promoted in this pass"

------------------------------------------------------------------------
-- Producer-chain archaeology.
------------------------------------------------------------------------

record ProducerArchaeology : Set where
  constructor producer-archaeology
  field
    publishedCorpusMonth : String
    releasedParserDumpCue : String
    parserDumpCueLink : String
    parserSourceCommit : String
    parserSourceCommitDate : String
    productionInputCarrier : String
    productionOutputCarrier : String
    publicFlnMapAvailable : Bool
    publicDerivedStatisticsAvailable : Bool
    exactUpstreamDumpIdentityPaid : Bool
    exactLocalSplitByteIdentityPaid : Bool
    exactExecutedParserRevisionPaid : Bool
    releasedParserMatchesDescribedMethodPaid : Bool
open ProducerArchaeology public

canonicalProducerArchaeology : ProducerArchaeology
canonicalProducerArchaeology = producer-archaeology
  "paper/methods: English Wikipedia snapshot provided in November 2014"
  "released first_link_txt.py comment: https://dumps.wikimedia.org/enwiki/20141008/"
  "https://github.com/marksibrahim/wikipedia_network/blob/master/code/first_link_txt.py"
  "9dd11de2676860751b02c1bbb0aeee0afb7b2710"
  "2015-10-04"
  "/users/m/s/msibrahi/full_wiki_data/small*.xml"
  "/users/m/s/msibrahi/v4/results/true_flnetwork/*.json -> combined FLN"
  true true false false false false

------------------------------------------------------------------------
-- Parser-policy comparison.
------------------------------------------------------------------------

record ParserPolicyComparison : Set where
  constructor parser-policy-comparison
  field
    methodsExcludeTemplates : Bool
    codeExcludesTemplates : Bool
    methodsExcludeParentheses : Bool
    codeExcludesParentheses : Bool
    methodsExcludeRefDiv : Bool
    codeExcludesRefDiv : Bool
    methodsFilterForeignNamespaces : Bool
    codeFiltersForeignNamespaces : Bool
    methodsClaimCommonFileExtensionFiltering : Bool
    releasedCodeFileExtensionFilterLocated : Bool
    equivalenceConclusionPaid : Bool
open ParserPolicyComparison public

releasedParserPolicyComparison : ParserPolicyComparison
releasedParserPolicyComparison = parser-policy-comparison
  true true true true true true true true true false false

firstParserEquivalenceResidual : String
firstParserEquivalenceResidual =
  "locate or reconstruct the common-image/audio-file-extension filter described in the methods appendix, or prove it redundant under the released namespace/prefix filter on the actual historical input"

firstCorpusIdentityResidual : String
firstCorpusIdentityResidual =
  "join the published November-2014 corpus description to the exact upstream Wikimedia dump that produced full_wiki_data/small*.xml; the released 20141008 comment is a producer cue, not same-object payment"

------------------------------------------------------------------------
-- Derived graph products remain downstream of producer identity.
------------------------------------------------------------------------

record DerivedProduct : Set where
  constructor derived-product
  field
    product : String
    publicLink : String
    dependsOnHistoricalFln : Bool
    canIdentifyHistoricalDump : Bool
open DerivedProduct public

flnMapProduct : DerivedProduct
flnMapProduct = derived-product
  "First Link Network map: article -> first link"
  "https://compstorylab.org/share/papers/ibrahim2016a/data.html"
  true false

traversalVisitsProduct : DerivedProduct
traversalVisitsProduct = derived-product
  "First Link Accumulation / traversal visits"
  "https://compstorylab.org/share/papers/ibrahim2016a/data.html"
  true false

pathLengthsProduct : DerivedProduct
pathLengthsProduct = derived-product
  "Network depth / path lengths"
  "https://compstorylab.org/share/papers/ibrahim2016a/data.html"
  true false

traversalFunnelsProduct : DerivedProduct
traversalFunnelsProduct = derived-product
  "Influence on flow / traversal funnels"
  "https://compstorylab.org/share/papers/ibrahim2016a/data.html"
  true false

------------------------------------------------------------------------
-- Snowball attribution/payment discipline.
------------------------------------------------------------------------

data PaperMonthCreatesDumpDay : Set where
data CodeCommentCreatesRunIdentity : Set where
data PublicFlnCreatesInputIdentity : Set where
data QidCreatesHistoricalEdge : Set where
data DeweyCreatesGraphEdge : Set where
data DerivedStatisticCreatesProducerIdentity : Set where
data ReleasedCodeCreatesExecutionReceipt : Set where

paperMonthDoesNotCreateDumpDay : PaperMonthCreatesDumpDay → ⊥
paperMonthDoesNotCreateDumpDay ()

codeCommentDoesNotCreateRunIdentity : CodeCommentCreatesRunIdentity → ⊥
codeCommentDoesNotCreateRunIdentity ()

publicFlnDoesNotCreateInputIdentity : PublicFlnCreatesInputIdentity → ⊥
publicFlnDoesNotCreateInputIdentity ()

qidDoesNotCreateHistoricalEdge : QidCreatesHistoricalEdge → ⊥
qidDoesNotCreateHistoricalEdge ()

deweyDoesNotCreateGraphEdge : DeweyCreatesGraphEdge → ⊥
deweyDoesNotCreateGraphEdge ()

derivedStatisticDoesNotCreateProducerIdentity : DerivedStatisticCreatesProducerIdentity → ⊥
derivedStatisticDoesNotCreateProducerIdentity ()

releasedCodeDoesNotCreateExecutionReceipt : ReleasedCodeCreatesExecutionReceipt → ⊥
releasedCodeDoesNotCreateExecutionReceipt ()

record IbrahimProducerSnowballBoundary : Set where
  constructor ibrahim-producer-snowball-boundary
  field
    primaryPaperAttributed : Bool
    releasedCodeAttributed : Bool
    onlineDataAttributed : Bool
    doiTravels : Bool
    qidTravelsAsIdentityOnly : Bool
    deweyTravelsAsNavigationOnly : Bool
    directLinksTravel : Bool
    publicationMonthSeparatedFromDumpIdentity : Bool
    sourceTreeSeparatedFromExecutedRevision : Bool
    derivedProductsSeparatedFromProducerIdentity : Bool
    parserMethodEquivalenceStillOpen : Bool
    historicalSameObjectJoinStillOpen : Bool
open IbrahimProducerSnowballBoundary public

canonicalIbrahimProducerSnowballBoundary : IbrahimProducerSnowballBoundary
canonicalIbrahimProducerSnowballBoundary =
  ibrahim-producer-snowball-boundary
    true true true true true true true true true true true true
