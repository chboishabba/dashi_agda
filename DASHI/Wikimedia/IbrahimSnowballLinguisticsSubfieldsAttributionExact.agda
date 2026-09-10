module DASHI.Wikimedia.IbrahimSnowballLinguisticsSubfieldsAttributionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.SourceProvenanceExact as Source
import DASHI.Culture.IPAPhoneticFeatureLatticeExact as IPA
import DASHI.Culture.PhonologicalFeatureMatrixContrastExact as Phonology
import DASHI.Culture.LinguisticAnthropologyTlureyPragmaticsBridgeExact as Pragmatics
import DASHI.Cognition.PNF.SpacyNumericProjection as Spacy

------------------------------------------------------------------------
-- IBRAHIM SNOWBALL: LINGUISTICS AND MAJOR SUBFIELDS
--
-- Navigation prior:
-- Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's First Link
-- Network", Journal of Computational Science 19 (2017), 21-30.
-- DOI 10.1016/j.jocs.2016.12.001.
--
-- Current EN/Wikidata inspection date: 2026-09-10.
-- Current EN Linguistics begins by describing linguistics as the scientific
-- study of language, so the current first-body-link probe is Linguistics ->
-- Language.  The subfield relations below are external discipline/navigation
-- coordinates.  They are not asserted to be Ibrahim's November-2014 edges
-- unless an exact historical carrier is separately inspected.
--
-- Attribution discipline:
-- QID, Wikipedia revision, DOI/canonical URL, source role, DASHI reconstruction
-- and theorem status remain independent.  Unresolved exact revision identity is
-- retained explicitly rather than replaced with an observation date.
------------------------------------------------------------------------

ibrahimSource : Attribution.AttributedSource
ibrahimSource = Attribution.mkDOISource
  "Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds"
  "Connecting every bit of knowledge: The structure of Wikipedia's First Link Network"
  "Journal of Computational Science 19, 21-30"
  "2017"
  "10.1016/j.jocs.2016.12.001"
  "https://doi.org/10.1016/j.jocs.2016.12.001"
  Attribution.academicArticleSource
  "historical Wikipedia first-link navigation/funnel prior only; not linguistic semantic or theorem authority"
  Attribution.publicAttribution

ibrahimSourceRoleReceipt : AttributionSnowball.SourceRoleSnowballReceipt ibrahimSource
ibrahimSourceRoleReceipt = AttributionSnowball.canonicalSourceRoleSnowballReceipt ibrahimSource

------------------------------------------------------------------------
-- Verified external identity coordinates.
------------------------------------------------------------------------

linguisticsQid : Identity.ExternalIdentityDemand
linguisticsQid = Identity.mkOptionalIdentityDemand
  "linguistics snowball" "linguistics identity" "Linguistics"
  Identity.wikidataQid (Identity.verified "Q8162" "Wikidata identity inspected 2026-09-10")

languageQid : Identity.ExternalIdentityDemand
languageQid = Identity.mkOptionalIdentityDemand
  "linguistics snowball" "language identity" "Language"
  Identity.wikidataQid (Identity.verified "Q315" "Wikidata identity inspected 2026-09-10")

phoneticsQid : Identity.ExternalIdentityDemand
phoneticsQid = Identity.mkOptionalIdentityDemand
  "linguistics snowball" "phonetics identity" "Phonetics"
  Identity.wikidataQid (Identity.verified "Q35395" "Wikidata identity inspected 2026-09-10")

phonologyQid : Identity.ExternalIdentityDemand
phonologyQid = Identity.mkOptionalIdentityDemand
  "linguistics snowball" "phonology identity" "Phonology"
  Identity.wikidataQid (Identity.verified "Q40998" "Wikidata identity inspected 2026-09-10")

morphologyQid : Identity.ExternalIdentityDemand
morphologyQid = Identity.mkOptionalIdentityDemand
  "linguistics snowball" "linguistic morphology identity" "Morphology (linguistics)"
  Identity.wikidataQid (Identity.verified "Q38311" "verified against biological-morphology false-positive Q183252")

syntaxQid : Identity.ExternalIdentityDemand
syntaxQid = Identity.mkOptionalIdentityDemand
  "linguistics snowball" "natural-language syntax identity" "Syntax"
  Identity.wikidataQid (Identity.verified "Q37437" "Wikidata identity inspected 2026-09-10")

semanticsQid : Identity.ExternalIdentityDemand
semanticsQid = Identity.mkOptionalIdentityDemand
  "linguistics snowball" "linguistic semantics identity" "Semantics"
  Identity.wikidataQid (Identity.verified "Q39645" "Wikidata identity inspected 2026-09-10")

pragmaticsQid : Identity.ExternalIdentityDemand
pragmaticsQid = Identity.mkOptionalIdentityDemand
  "linguistics snowball" "pragmatics identity" "Pragmatics"
  Identity.wikidataQid (Identity.verified "Q181839" "verified against article/work false-positive Q38500704")

sociolinguisticsQid : Identity.ExternalIdentityDemand
sociolinguisticsQid = Identity.mkOptionalIdentityDemand
  "linguistics snowball" "sociolinguistics identity" "Sociolinguistics"
  Identity.wikidataQid (Identity.verified "Q160845" "Wikidata identity inspected 2026-09-10")

------------------------------------------------------------------------
-- Wikipedia revision is a separate coordinate.  The current observations are
-- bounded by date, but exact page/revision/hash receipts have not yet been
-- acquired in this tranche; no placeholder revision is fabricated.
------------------------------------------------------------------------

data WikipediaRevisionBinding : Set where
  exactRevisionBound : Source.WikipediaRevisionReceipt -> WikipediaRevisionBinding
  revisionPending : String -> WikipediaRevisionBinding

record LinguisticSnowballNode : Set where
  constructor linguistic-snowball-node
  field
    title : String
    qid : Identity.ExternalIdentityDemand
    wikipediaRevision : WikipediaRevisionBinding
    currentExternalRelation : String
    relationRole : String
    canonicalDashiOwnerObserved : Bool
    reusableDashiSubstrateObserved : Bool
    sourceLaneObserved : Bool
    empiricalProducerObserved : Bool
    lexicalFalsePositiveRisk : Bool
    residual : String
open LinguisticSnowballNode public

linguisticsNode : LinguisticSnowballNode
linguisticsNode = linguistic-snowball-node
  "Linguistics" linguisticsQid
  (revisionPending "current EN observation inspected 2026-09-10; exact page/revision/hash still to acquire")
  "current EN first-body-link: Linguistics -> Language"
  "literal current navigation probe; not backdated to Ibrahim 2014"
  false true true false false
  "canonical repo-wide Linguistics parent consolidation remains useful"

phoneticsNode : LinguisticSnowballNode
phoneticsNode = linguistic-snowball-node
  "Phonetics" phoneticsQid
  (revisionPending "current EN relation inspected 2026-09-10")
  "Phonetics -> Linguistics"
  "current navigation/discipline relation"
  true true true false false
  "architecture/source paid by IPA lattice; first concrete event transcription remains open"

phonologyNode : LinguisticSnowballNode
phonologyNode = linguistic-snowball-node
  "Phonology" phonologyQid
  (revisionPending "current EN relation inspected 2026-09-10")
  "Phonology -> Linguistics"
  "current navigation/discipline relation"
  true true true false false
  "feature-matrix and language-relative contrast architecture paid; concrete language inventory remains open"

morphologyNode : LinguisticSnowballNode
morphologyNode = linguistic-snowball-node
  "Morphology (linguistics)" morphologyQid
  (revisionPending "current EN/Wikidata discipline relation inspected 2026-09-10")
  "linguistic morphology is a linguistics subfield concerned with word/internal morpheme structure"
  "discipline/navigation relation; not inferred from every lexical occurrence of morphology"
  false true false false true
  "spaCy morphology annotations are observation substrate only; canonical linguistic morphology/source owner still open"

syntaxNode : LinguisticSnowballNode
syntaxNode = linguistic-snowball-node
  "Syntax" syntaxQid
  (revisionPending "current EN/Wikidata discipline relation inspected 2026-09-10")
  "syntax is a linguistics subfield concerned with sentence/phrase structure"
  "discipline/navigation relation; programming-language syntax excluded"
  false true false false true
  "dependency-parser observations exist; canonical natural-language syntax/source owner still open"

semanticsNode : LinguisticSnowballNode
semanticsNode = linguistic-snowball-node
  "Semantics" semanticsQid
  (revisionPending "current EN/Wikidata discipline relation inspected 2026-09-10")
  "semantics studies linguistic meaning"
  "discipline/navigation relation; formal-logic semantics is reusable but not identical"
  false true false false true
  "natural-language semantic owner/source bridge remains open; do not silently promote formal logic semantics"

pragmaticsNode : LinguisticSnowballNode
pragmaticsNode = linguistic-snowball-node
  "Pragmatics" pragmaticsQid
  (revisionPending "current EN/Wikidata discipline relation inspected 2026-09-10")
  "pragmatics studies context-dependent language use/meaning"
  "discipline/navigation relation"
  false true true false false
  "Tlurey/Hymes/Duranti bridge pays a strong situated-pragmatics seam, not all pragmatics"

sociolinguisticsNode : LinguisticSnowballNode
sociolinguisticsNode = linguistic-snowball-node
  "Sociolinguistics" sociolinguisticsQid
  (revisionPending "current EN/Wikidata discipline relation inspected 2026-09-10")
  "sociolinguistics studies language in social context and variation"
  "discipline/navigation relation"
  false true false false false
  "linguistic anthropology/social-governance substrate strong; canonical sociolinguistics/source producer remains open"

------------------------------------------------------------------------
-- Concrete reuse/status corrections.
------------------------------------------------------------------------

phoneticArchitectureReceipt : IPA.IPAPhoneticFeatureBoundary
phoneticArchitectureReceipt = IPA.canonicalIPAPhoneticFeatureBoundary

phonologyArchitectureReceipt : Phonology.PhonologicalFeatureMatrixBoundary
phonologyArchitectureReceipt = Phonology.canonicalPhonologicalFeatureMatrixBoundary

pragmaticsSubstrateReceipt : Pragmatics.LinguisticAnthropologyTlureyBoundary
pragmaticsSubstrateReceipt = Pragmatics.canonicalLinguisticAnthropologyTlureyBoundary

spacyObservationBoundary : Spacy.SpacyProjectionBoundary
spacyObservationBoundary = Spacy.canonicalSpacyProjectionBoundary

------------------------------------------------------------------------
-- Snowball priority after quotienting the current repository.
------------------------------------------------------------------------

record LinguisticsSnowballPriority : Set where
  constructor linguistics-snowball-priority
  field
    linguisticsParentConsolidation : Bool
    morphologyCanonicalOwner : Bool
    syntaxCanonicalOwner : Bool
    naturalLanguageSemanticsOwner : Bool
    generalPragmaticsOwner : Bool
    sociolinguisticsOwner : Bool
    phoneticsArchitectureStillMissing : Bool
    phonologyArchitectureStillMissing : Bool
    firstShortestLeaf : String
open LinguisticsSnowballPriority public

currentLinguisticsPriority : LinguisticsSnowballPriority
currentLinguisticsPriority = linguistics-snowball-priority
  true true true true false true false false
  "Morphology: reuse spaCy morphology observations but add a source-bounded linguistic morphology owner"

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data ParserMorphologyCreatesLinguisticMorphologyTheory : Set where
data AgdaSyntaxCreatesNaturalLanguageSyntax : Set where
data FormalLogicSemanticsCreatesNaturalLanguageSemantics : Set where
data TlureyPragmaticsExhaustsPragmatics : Set where
data QidCreatesFormalDependency : Set where
data CurrentWikipediaRelationCreatesIbrahim2014Edge : Set where
data VerifiedQidReplacesPublicationIdentifier : Set where
data WikipediaOrWikidataCreatesLinguisticAuthority : Set where

parserMorphologyDoesNotCreateTheory : ParserMorphologyCreatesLinguisticMorphologyTheory -> ⊥
parserMorphologyDoesNotCreateTheory ()

agdaSyntaxIsNotNaturalLanguageSyntax : AgdaSyntaxCreatesNaturalLanguageSyntax -> ⊥
agdaSyntaxIsNotNaturalLanguageSyntax ()

formalLogicSemanticsIsNotAutomaticallyNaturalLanguageSemantics :
  FormalLogicSemanticsCreatesNaturalLanguageSemantics -> ⊥
formalLogicSemanticsIsNotAutomaticallyNaturalLanguageSemantics ()

tlureyPragmaticsDoesNotExhaustPragmatics : TlureyPragmaticsExhaustsPragmatics -> ⊥
tlureyPragmaticsDoesNotExhaustPragmatics ()

qidDoesNotCreateFormalDependency : QidCreatesFormalDependency -> ⊥
qidDoesNotCreateFormalDependency ()

currentWikipediaRelationDoesNotBackdateHistoricalEdge :
  CurrentWikipediaRelationCreatesIbrahim2014Edge -> ⊥
currentWikipediaRelationDoesNotBackdateHistoricalEdge ()

qidDoesNotReplacePublicationIdentifier : VerifiedQidReplacesPublicationIdentifier -> ⊥
qidDoesNotReplacePublicationIdentifier ()

wikimediaDoesNotCreateLinguisticAuthority : WikipediaOrWikidataCreatesLinguisticAuthority -> ⊥
wikimediaDoesNotCreateLinguisticAuthority ()

record LinguisticsSnowballAttributionBoundary : Set where
  constructor linguistics-snowball-attribution-boundary
  field
    qidsRequestedAndRetained : Bool
    wikipediaRevisionSeparateFromObservationDate : Bool
    exactRevisionMayRemainExplicitlyPending : Bool
    doiAndQidRemainIndependent : Bool
    sourceRolesSnowball : Bool
    lexicalFalsePositivesDoNotPayCoverage : Bool
    currentEdgesNotBackdatedTo2014 : Bool
    externalIdentityCreatesAuthority : Bool
    currentAxisVocabularyClaimedComplete : Bool
open LinguisticsSnowballAttributionBoundary public

canonicalLinguisticsSnowballAttributionBoundary : LinguisticsSnowballAttributionBoundary
canonicalLinguisticsSnowballAttributionBoundary =
  linguistics-snowball-attribution-boundary true true true true true true true false false
