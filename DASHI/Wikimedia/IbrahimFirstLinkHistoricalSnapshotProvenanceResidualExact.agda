module DASHI.Wikimedia.IbrahimFirstLinkHistoricalSnapshotProvenanceResidualExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.IbrahimSnowballSymbolicVerificationDeweyQidDoiBidiExact as Dewey
import DASHI.Wikimedia.WikipediaFirstLinkNetworkExact as FLN

------------------------------------------------------------------------
-- HIGHEST-ALPHA IBRAHIM SOURCE ARCHAEOLOGY RESIDUAL
--
-- Published paper + author blog describe the English-Wikipedia snapshot as
-- November 2014.  The public parser source explicitly references the
-- enwiki/20141008 dump directory.  The public FLN constructor consumes chopped
-- local small*.xml files and does not independently identify their upstream
-- dump.  Therefore exact historical input identity remains unresolved.
--
-- Acquisition may snowball across later/sideways evidence, but payment order is:
-- exact dump artifact -> parser/code identity -> parser-equivalent execution ->
-- result artifact/same-object match.  No source cue may silently skip that chain.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Stable external identities.
------------------------------------------------------------------------

mkQid : String → String → Identity.ExternalIdentityDemand
mkQid label qid = Identity.mkOptionalIdentityDemand
  "Ibrahim historical FLN snapshot provenance residual"
  "verified external identity only"
  label Identity.wikidataQid
  (Identity.verified qid
    "Wikidata identity inspected 2026-09-11; QID does not identify historical dump, parser input, graph result or publication claim")

wikipediaQid : Identity.ExternalIdentityDemand
wikipediaQid = mkQid "Wikipedia" "Q52"

englishWikipediaQid : Identity.ExternalIdentityDemand
englishWikipediaQid = mkQid "English Wikipedia" "Q328"

firstLinkNetworkQid : Identity.ExternalIdentityDemand
firstLinkNetworkQid = Identity.mkOptionalIdentityDemand
  "Ibrahim historical FLN snapshot provenance residual"
  "external concept/data-object identity"
  "Wikipedia First Link Network as constructed by Ibrahim-Danforth-Dodds"
  Identity.wikidataQid
  (Identity.unresolved
    "no exact standalone Wikidata item promoted for the research FLN object")

historicalDumpQid : Identity.ExternalIdentityDemand
historicalDumpQid = Identity.mkOptionalIdentityDemand
  "Ibrahim historical FLN snapshot provenance residual"
  "external artifact identity"
  "exact English Wikipedia XML dump used for published FLN"
  Identity.wikidataQid
  (Identity.unresolved
    "dump identity is an artifact/date/file receipt problem; no QID substitutes for exact file identity")

------------------------------------------------------------------------
-- Dewey is retained, but no shelf classification is allowed to settle corpus
-- identity or method provenance.
------------------------------------------------------------------------

englishWikipediaDewey : Dewey.DeweyCoordinate
englishWikipediaDewey = Dewey.mkUnresolvedDewey
  "English Wikipedia historical corpus"
  "no exact inspected DDC value promoted; library classification cannot pay dump identity"

firstLinkNetworkDewey : Dewey.DeweyCoordinate
firstLinkNetworkDewey = Dewey.mkUnresolvedDewey
  "Wikipedia First Link Network / network-science research object"
  "no exact inspected DDC value promoted; network-science shelf choice is navigation only"

------------------------------------------------------------------------
-- Primary/publication/data/code attribution.
------------------------------------------------------------------------

ibrahimPaperSource : Attribution.AttributedSource
ibrahimPaperSource = Attribution.mkDOISource
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds"
  "Connecting every bit of knowledge: The structure of Wikipedia's First Link Network"
  "Journal of Computational Science 19, 21-30"
  "2017"
  "10.1016/j.jocs.2016.12.001"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  Attribution.academicArticleSource
  "primary research publication; states English Wikipedia as of November 2014 but does not by that prose alone identify the exact dump file/day"
  Attribution.publicAttribution

ibrahimArxivIdentity : Identity.ExternalIdentityDemand
ibrahimArxivIdentity = Identity.mkOptionalIdentityDemand
  "Ibrahim historical FLN snapshot provenance residual"
  "publication identity"
  "Connecting every bit of knowledge preprint"
  Identity.arxiv
  (Identity.verified "1605.00309"
    "arXiv publication identity retained alongside DOI; neither pays exact dump identity")

projectSiteSource : Attribution.AttributedSource
projectSiteSource = Attribution.mkNoDOISource
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds / Computational Story Lab"
  "Connecting Every Bit of Knowledge project site"
  "Computational Story Lab"
  "2017"
  "https://compstorylab.org/share/papers/ibrahim2016a/index.html"
  Attribution.institutionalSource
  "author-hosted project landing page linking paper, notebooks, code and data; navigation/source provenance only"
  Attribution.publicAttribution

dataPageSource : Attribution.AttributedSource
dataPageSource = Attribution.mkNoDOISource
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds / Computational Story Lab"
  "First Link Network data page"
  "Computational Story Lab project appendix"
  "2017"
  "https://compstorylab.org/share/papers/ibrahim2016a/data.html"
  Attribution.institutionalSource
  "author-hosted data-artifact surface for FLN/results; result availability does not establish exact upstream XML dump identity"
  Attribution.publicAttribution

publicCodeRepositorySource : Attribution.AttributedSource
publicCodeRepositorySource = Attribution.mkNoDOISource
  "Mark Ibrahim"
  "wikipedia_network"
  "GitHub research-code repository"
  "2015"
  "https://github.com/marksibrahim/wikipedia_network"
  (Attribution.namedSourceKind "research code")
  "author-controlled code repository; code provenance is distinct from publication prose and data-object provenance"
  Attribution.publicAttribution

firstLinkParserSource : Attribution.AttributedSource
firstLinkParserSource = Attribution.mkNoDOISource
  "Mark Ibrahim"
  "code/first_link_txt.py"
  "wikipedia_network GitHub repository; blob a830c47905d4cde90876e1097f2620f4f19a63df"
  "2015"
  "https://github.com/marksibrahim/wikipedia_network/blob/master/code/first_link_txt.py"
  (Attribution.namedSourceKind "research parser source code")
  "primary parser source; explicitly contains enwiki/20141008 dump URL and first-link filtering rules; code comment is a provenance cue, not proof that this exact dump generated the published FLN"
  Attribution.publicAttribution

flnConstructorSource : Attribution.AttributedSource
flnConstructorSource = Attribution.mkNoDOISource
  "Mark Ibrahim"
  "code/create_fln.py"
  "wikipedia_network GitHub repository; blob 595f7f52ffc03e8a9542964b9dd3fffbfae87fca"
  "2015"
  "https://github.com/marksibrahim/wikipedia_network/blob/master/code/create_fln.py"
  (Attribution.namedSourceKind "research processing source code")
  "primary constructor source; imports first_link_txt and consumes local chopped small*.xml files, but does not identify the upstream Wikimedia dump file"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Source cues remain independently attributable.
------------------------------------------------------------------------

data HistoricalSnapshotCue : Set where
  publicationNovember2014 : HistoricalSnapshotCue
  authorBlogNovember2014 : HistoricalSnapshotCue
  parserOctober08DumpReference : HistoricalSnapshotCue
  localChoppedXmlInput : HistoricalSnapshotCue
  publicResultDataArtifact : HistoricalSnapshotCue

cueValue : HistoricalSnapshotCue → String
cueValue publicationNovember2014 = "publication prose: English Wikipedia as of November 2014"
cueValue authorBlogNovember2014 = "author blog: snapshot in November 2014"
cueValue parserOctober08DumpReference = "parser source: https://dumps.wikimedia.org/enwiki/20141008/"
cueValue localChoppedXmlInput = "constructor input: /users/m/s/msibrahi/full_wiki_data/small*.xml"
cueValue publicResultDataArtifact = "author-hosted FLN/result data artifact"

data SnapshotResolution : Set where
  exactDumpUnresolved : SnapshotResolution
  exactDumpVerified : String → String → SnapshotResolution

record HistoricalFLNProvenanceReceipt : Set where
  constructor historical-fln-provenance-receipt
  field
    publicationCue : HistoricalSnapshotCue
    blogCue : HistoricalSnapshotCue
    parserCue : HistoricalSnapshotCue
    constructorCue : HistoricalSnapshotCue
    resultCue : HistoricalSnapshotCue
    parserBlobSha : String
    parserRepositoryCommit : String
    constructorBlobSha : String
    exactInputDump : SnapshotResolution
    exactDumpFileHashPaid : Bool
    choppedXmlSameObjectWithDumpPaid : Bool
    parserEquivalentExecutionPaid : Bool
    reproducedGraphSameObjectPaid : Bool
    sourceCueDiscrepancyRetained : Bool
    laterCueMayRewriteEarlierSource : Bool
open HistoricalFLNProvenanceReceipt public

currentHistoricalFLNReceipt : HistoricalFLNProvenanceReceipt
currentHistoricalFLNReceipt = historical-fln-provenance-receipt
  publicationNovember2014
  authorBlogNovember2014
  parserOctober08DumpReference
  localChoppedXmlInput
  publicResultDataArtifact
  "a830c47905d4cde90876e1097f2620f4f19a63df"
  "9dd11de2676860751b02c1bbb0aeee0afb7b2710"
  "595f7f52ffc03e8a9542964b9dd3fffbfae87fca"
  exactDumpUnresolved
  false false false false
  true false

------------------------------------------------------------------------
-- Exact nonfactorability 1: a coarse historical-snapshot label cannot recover
-- exact dump identity.
------------------------------------------------------------------------

data SnapshotCase : Set where
  sameHistoricalFLNOctoberInput sameHistoricalFLNNovemberInput : SnapshotCase

data HistoricalLabel : Set where sameHistoricalFLNLabel : HistoricalLabel
data DumpIdentity : Set where october08Candidate novemberCandidate : DumpIdentity

historicalLabel : SnapshotCase → HistoricalLabel
historicalLabel _ = sameHistoricalFLNLabel

dumpIdentity : SnapshotCase → DumpIdentity
dumpIdentity sameHistoricalFLNOctoberInput = october08Candidate
dumpIdentity sameHistoricalFLNNovemberInput = novemberCandidate

snapshotIdentityDefect : INF.NonFactorabilityWitness historicalLabel dumpIdentity
snapshotIdentityDefect = INF.nonFactorabilityWitness
  sameHistoricalFLNOctoberInput sameHistoricalFLNNovemberInput refl (λ ())

historicalFLNLabelCannotFactorExactDumpIdentity :
  INF.FactorsThrough historicalLabel dumpIdentity → ⊥
historicalFLNLabelCannotFactorExactDumpIdentity =
  INF.witnessRulesOutEveryFlatFactorisation snapshotIdentityDefect

------------------------------------------------------------------------
-- Exact nonfactorability 2: same parser code cannot recover graph identity if
-- the input corpus differs.
------------------------------------------------------------------------

data ParserRunCase : Set where
  sameParserDifferentInputA sameParserDifferentInputB : ParserRunCase

data ParserSurface : Set where sameParserBlob : ParserSurface
data GraphIdentity : Set where graphFromInputA graphFromInputB : GraphIdentity

parserSurface : ParserRunCase → ParserSurface
parserSurface _ = sameParserBlob

graphIdentity : ParserRunCase → GraphIdentity
graphIdentity sameParserDifferentInputA = graphFromInputA
graphIdentity sameParserDifferentInputB = graphFromInputB

parserInputDefect : INF.NonFactorabilityWitness parserSurface graphIdentity
parserInputDefect = INF.nonFactorabilityWitness
  sameParserDifferentInputA sameParserDifferentInputB refl (λ ())

parserBlobCannotFactorHistoricalGraphIdentity :
  INF.FactorsThrough parserSurface graphIdentity → ⊥
parserBlobCannotFactorHistoricalGraphIdentity =
  INF.witnessRulesOutEveryFlatFactorisation parserInputDefect

------------------------------------------------------------------------
-- Payment order / acquisition freedom.
------------------------------------------------------------------------

data HistoricalPaymentStage : Set where
  exactDumpArtifactIdentity : HistoricalPaymentStage
  exactDumpHash : HistoricalPaymentStage
  choppedXmlSameObject : HistoricalPaymentStage
  parserSemantics : HistoricalPaymentStage
  parserEquivalentReproduction : HistoricalPaymentStage
  publishedResultSameObject : HistoricalPaymentStage

record HistoricalSnowballPolicy : Set where
  constructor historical-snowball-policy
  field
    laterEvidenceMayBeAcquiredEarly : Bool
    laterEvidenceMaySkipDumpIdentity : Bool
    paperMonthEqualsExactDumpDay : Bool
    parserCommentEqualsExecutionReceipt : Bool
    resultArtifactEqualsInputProvenance : Bool
    currentWikipediaMayPayHistoricalEdge : Bool
    discrepancyMustRemainAppendOnly : Bool
    exactDumpIdentityIsFirstHistoricalPaymentResidual : Bool
open HistoricalSnowballPolicy public

canonicalHistoricalSnowballPolicy : HistoricalSnowballPolicy
canonicalHistoricalSnowballPolicy = historical-snowball-policy
  true false false false false false true true

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data NovemberLabelCreatesExactDumpDay : Set where
data ParserCommentCreatesExecutedInputIdentity : Set where
data PublicFLNDataCreatesDumpProvenance : Set where
data CurrentEdgeCreatesHistoricalEdge : Set where
data OctoberCueCancelsNovemberPublicationCue : Set where
data NovemberCueCancelsOctoberParserCue : Set where
data QidCreatesSnapshotIdentity : Set where
data DeweyCreatesSnapshotIdentity : Set where

novemberLabelDoesNotCreateExactDumpDay : NovemberLabelCreatesExactDumpDay → ⊥
novemberLabelDoesNotCreateExactDumpDay ()

parserCommentDoesNotCreateExecutedInputIdentity : ParserCommentCreatesExecutedInputIdentity → ⊥
parserCommentDoesNotCreateExecutedInputIdentity ()

publicFLNDataDoesNotCreateDumpProvenance : PublicFLNDataCreatesDumpProvenance → ⊥
publicFLNDataDoesNotCreateDumpProvenance ()

currentEdgeDoesNotCreateHistoricalEdge : CurrentEdgeCreatesHistoricalEdge → ⊥
currentEdgeDoesNotCreateHistoricalEdge ()

octoberCueDoesNotEraseNovemberCue : OctoberCueCancelsNovemberPublicationCue → ⊥
octoberCueDoesNotEraseNovemberCue ()

novemberCueDoesNotEraseOctoberCue : NovemberCueCancelsOctoberParserCue → ⊥
novemberCueDoesNotEraseOctoberCue ()

qidDoesNotCreateSnapshotIdentity : QidCreatesSnapshotIdentity → ⊥
qidDoesNotCreateSnapshotIdentity ()

deweyDoesNotCreateSnapshotIdentity : DeweyCreatesSnapshotIdentity → ⊥
deweyDoesNotCreateSnapshotIdentity ()

------------------------------------------------------------------------
-- Existing FLN semantic boundary remains authoritative; this owner only pays
-- source-object archaeology and exact historical corpus identity debt.
------------------------------------------------------------------------

firstLinkBoundary : FLN.WikipediaFirstLinkBoundary
firstLinkBoundary = FLN.canonicalWikipediaFirstLinkBoundary

record HistoricalSnapshotProvenanceBoundary : Set where
  constructor historical-snapshot-provenance-boundary
  field
    doiRetained : Bool
    arxivRetained : Bool
    qidsRetained : Bool
    deweyExplicitlyUnresolved : Bool
    canonicalProjectDataCodeLinksRetained : Bool
    publicationAndCodeCuesBothRetained : Bool
    exactDumpStillUnresolved : Bool
    parserBlobPinned : Bool
    constructorBlobPinned : Bool
    sameObjectDumpToChunksStillRequired : Bool
    reproductionStillRequired : Bool
    historicalCurrentEdgeFirewallRetained : Bool
    presentSourceCueVocabularyClaimedComplete : Bool
open HistoricalSnapshotProvenanceBoundary public

canonicalHistoricalSnapshotProvenanceBoundary : HistoricalSnapshotProvenanceBoundary
canonicalHistoricalSnapshotProvenanceBoundary =
  historical-snapshot-provenance-boundary
    true true true true true true true true true true true true false
