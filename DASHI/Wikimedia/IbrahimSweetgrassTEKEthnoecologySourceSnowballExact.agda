module DASHI.Wikimedia.IbrahimSweetgrassTEKEthnoecologySourceSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Wikimedia.Ibrahim36927PantsColourTextileSweetgrassSnowballExact as Cross
import DASHI.Wikimedia.WikipediaAllPairsPrunedMergeSnowballExact as AllPairs
import DASHI.Interop.SweetgrassCarrierSpine as Sweetgrass

------------------------------------------------------------------------
-- BRAIDING SWEETGRASS -> TEK -> ETHNOECOLOGY / TRADITIONAL KNOWLEDGE
--
-- External ontology coordinates are retained as subject/context relations.
-- They do not replace Robin Wall Kimmerer's authorship, Citizen Potawatomi
-- context, the book itself, or the repo's explicit attribution boundaries.
--
-- Coordinates inspected 2026-09-11:
--   Braiding Sweetgrass              Q85748689
--   traditional ecological knowledge Q7832334
--   ethnoecology                      Q1371429
--   traditional knowledge             Q1428168
--
-- Separate scholarly source coordinate:
--   Henry P. Huntington, "Using Traditional Ecological Knowledge in Science:
--   Methods and Applications", Ecological Applications 10(5), 2000,
--   DOI 10.1890/1051-0761(2000)010[1270:UTEKIS]2.0.CO;2
------------------------------------------------------------------------

tekQid : Identity.ExternalIdentityDemand
tekQid = Identity.mkOptionalIdentityDemand
  "Sweetgrass subject/context snowball"
  "traditional ecological knowledge external identity"
  "traditional ecological knowledge"
  Identity.wikidataQid
  (Identity.verified "Q7832334" "Wikidata oldid 2499526498 inspected 2026-09-11")

ethnoecologyQid : Identity.ExternalIdentityDemand
ethnoecologyQid = Identity.mkOptionalIdentityDemand
  "Sweetgrass subject/context snowball"
  "ethnoecology external identity"
  "ethnoecology"
  Identity.wikidataQid
  (Identity.verified "Q1371429" "Wikidata inspected 2026-09-11")

traditionalKnowledgeQid : Identity.ExternalIdentityDemand
traditionalKnowledgeQid = Identity.mkOptionalIdentityDemand
  "Sweetgrass subject/context snowball"
  "traditional knowledge external identity"
  "traditional knowledge"
  Identity.wikidataQid
  (Identity.verified "Q1428168" "Wikidata inspected 2026-09-11")

record ContextEdge : Set where
  constructor context-edge
  field
    source : String
    target : String
    relation : String
    evidenceReference : String
    replacesAuthorship : Bool
    createsScientificProof : Bool
open ContextEdge public

sweetgrassToTEK : ContextEdge
sweetgrassToTEK = context-edge
  "Braiding Sweetgrass/Q85748689"
  "traditional ecological knowledge/Q7832334"
  "main-subject/context coordinate"
  "Wikidata subject relation inspected 2026-09-11"
  false false

tekToEthnoecology : ContextEdge
tekToEthnoecology = context-edge
  "traditional ecological knowledge/Q7832334"
  "ethnoecology/Q1371429"
  "facet-of"
  "Wikidata facet-of relation imported from English Wikipedia and retained as ontology metadata"
  false false

tekToTraditionalKnowledge : ContextEdge
tekToTraditionalKnowledge = context-edge
  "traditional ecological knowledge/Q7832334"
  "traditional knowledge/Q1428168"
  "subclass/context"
  "Wikidata subclass relation inspected 2026-09-11"
  false false

record ScholarlySourceCoordinate : Set where
  constructor scholarly-source-coordinate
  field
    author : String
    title : String
    publication : String
    year : String
    doi : String
    role : String
    isKimmererAuthorshipSource : Bool
    importsProof : Bool
open ScholarlySourceCoordinate public

huntingtonTEKMethods : ScholarlySourceCoordinate
huntingtonTEKMethods = scholarly-source-coordinate
  "Henry P. Huntington"
  "Using Traditional Ecological Knowledge in Science: Methods and Applications"
  "Ecological Applications 10(5)"
  "2000"
  "10.1890/1051-0761(2000)010[1270:UTEKIS]2.0.CO;2"
  "independent scholarly source about methods/applications of traditional ecological knowledge in science"
  false false

------------------------------------------------------------------------
-- Attribution and knowledge-role boundary.
------------------------------------------------------------------------

record SweetgrassKnowledgeBoundary : Set where
  constructor sweetgrass-knowledge-boundary
  field
    kimmererAuthorshipRetained : Bool
    bookIdentityRetained : Bool
    culturalNationContextRetained : Bool
    tekSubjectCoordinateRetained : Bool
    ethnoecologyCoordinateRetained : Bool
    traditionalKnowledgeCoordinateRetained : Bool
    independentScientificSourceRetainedSeparately : Bool
    ontologyParentReplacesSituatedKnowledge : Bool
    externalScientificPaperReplacesKimmererAttribution : Bool
    sweetgrassBraidMotifCreatesMathematicalTheorem : Bool
    allPairsComparisonAllowed : Bool
open SweetgrassKnowledgeBoundary public

canonicalSweetgrassKnowledgeBoundary : SweetgrassKnowledgeBoundary
canonicalSweetgrassKnowledgeBoundary = sweetgrass-knowledge-boundary
  true true true true true true true false false false true

data TEKQidEqualsKimmererClaim : Set where
data EthnoecologyExhaustsTraditionalKnowledge : Set where
data ScholarlyTEKPaperCreatesSweetgrassAttribution : Set where
data CulturalBraidCreatesMathematicalBraidAuthority : Set where

tekQidDoesNotReplaceClaim : TEKQidEqualsKimmererClaim → ⊥
tekQidDoesNotReplaceClaim ()

ethnoecologyDoesNotExhaustKnowledge : EthnoecologyExhaustsTraditionalKnowledge → ⊥
ethnoecologyDoesNotExhaustKnowledge ()

paperDoesNotCreateBookAttribution : ScholarlyTEKPaperCreatesSweetgrassAttribution → ⊥
paperDoesNotCreateBookAttribution ()

culturalBraidDoesNotCreateMathAuthority : CulturalBraidCreatesMathematicalBraidAuthority → ⊥
culturalBraidDoesNotCreateMathAuthority ()

crossDomainBoundary : Cross.Ibrahim369ColourTextileBoundary
crossDomainBoundary = Cross.canonicalIbrahim369ColourTextileBoundary

allPairsBoundary : AllPairs.WikipediaAllPairsBoundary
allPairsBoundary = AllPairs.canonicalWikipediaAllPairsBoundary
