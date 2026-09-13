module DASHI.Wikimedia.IbrahimCountryCommunityKnowledgeAuthorityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapExact as Roadmap

------------------------------------------------------------------------
-- COUNTRY / COMMUNITY / KNOWLEDGE / AUTHORITY / SOCIETY-STATE BRIDGE
--
-- This is the first concrete payment selected by the Ibrahim-guided roadmap.
-- It is a projection across existing DASHI owners, not a replacement owner for
-- Indigenous knowledge, Country, community, society, state, science or law.
------------------------------------------------------------------------

data BridgeCoordinateKind : Set where
  placeCountry : BridgeCoordinateKind
  community : BridgeCoordinateKind
  knowledge : BridgeCoordinateKind
  powerAuthority : BridgeCoordinateKind
  society : BridgeCoordinateKind
  state : BridgeCoordinateKind

record BridgeCoordinate : Set where
  constructor bridge-coordinate
  field
    kind : BridgeCoordinateKind
    title : String
    existingDashiSurface : String
    authorityReading : String
open BridgeCoordinate public

countryCoordinate : BridgeCoordinate
countryCoordinate = bridge-coordinate placeCountry
  "Place / Country"
  "IndigenousKnowledgeStoryTwoEyedSeeingBidiExact; KimmererTwoEyedSeeingInterpretationBoundaryExact; Mabo/Country/SensibLaw owners; LESCountryExternalityRealisationExact"
  "place relation and Country/custodial authority require community-specific source/authority receipts; geography alone is insufficient"

communityCoordinate : BridgeCoordinate
communityCoordinate = bridge-coordinate community
  "Community"
  "CommunityConnectednessTopologyExact; CulturalMembershipBoundaryExact; Kimmerer/Two-Eyed and situated-community consumers"
  "community membership, representation and authority are situated; external classification does not create spokesperson status"

knowledgeCoordinate : BridgeCoordinate
knowledgeCoordinate = bridge-coordinate knowledge
  "Knowledge"
  "MultiObserverScienceQuotient; SituatedFormalisationBoundaryExact; IndigenousKnowledgeTwoEyedValidation; source/provenance owners"
  "knowledge role records method/source/observer/authority; scientific validation is one possible role, not the universal parent of all knowledge"

authorityCoordinate : BridgeCoordinate
authorityCoordinate = bridge-coordinate powerAuthority
  "Power / Authority"
  "Governance; SensibLaw; Mabo sovereignty; CulturalProvenanceBoundaryCore; authority/non-descent owners"
  "possession of institutional power, legal authority, community authority, custodial authority and epistemic authority are distinct coordinates"

societyCoordinate : BridgeCoordinate
societyCoordinate = bridge-coordinate society
  "Society"
  "CulturalMembershipBoundaryExact; social-ecology/culture/governance and SocialScience funnel substrates"
  "society-scale claims require an explicit aggregation/observer scope; community evidence does not silently become society-wide evidence"

stateCoordinate : BridgeCoordinate
stateCoordinate = bridge-coordinate state
  "State"
  "Governance; SensibLaw; Mabo/sovereignty; PoliticalSciencePolitics bridge; State parent audit"
  "state, government, nation, society and non-state authority remain distinct; state recognition is not the source of every antecedent authority"

------------------------------------------------------------------------
-- Typed relation roles. The same pair may support more than one relation, but
-- no relation is created merely because Wikipedia or Dewey places concepts
-- nearby.
------------------------------------------------------------------------

data BridgeRelationKind : Set where
  situatedIn : BridgeRelationKind
  heldBy : BridgeRelationKind
  informs : BridgeRelationKind
  governs : BridgeRelationKind
  recognisedBy : BridgeRelationKind
  studies : BridgeRelationKind
  aggregatesTo : BridgeRelationKind
  conflictsWith : BridgeRelationKind

record PluralBridgeEdge : Set where
  constructor plural-bridge-edge
  field
    from : BridgeCoordinate
    to : BridgeCoordinate
    relation : BridgeRelationKind
    dashiBasis : String
    sourceBoundaryRequired : Bool
    authorityBoundaryRequired : Bool
    semanticIdentityClaimed : Bool
open PluralBridgeEdge public

countryCommunityEdge : PluralBridgeEdge
countryCommunityEdge = plural-bridge-edge
  countryCoordinate communityCoordinate situatedIn
  "existing Country/community/Indigenous-knowledge owners retain place, community and custodial relation together"
  true true false

communityKnowledgeEdge : PluralBridgeEdge
communityKnowledgeEdge = plural-bridge-edge
  communityCoordinate knowledgeCoordinate heldBy
  "Two-Eyed/Kimmerer and situated-knowledge owners permit community-situated knowledge without making community membership sufficient for every claim"
  true true false

knowledgeAuthorityEdge : PluralBridgeEdge
knowledgeAuthorityEdge = plural-bridge-edge
  knowledgeCoordinate authorityCoordinate informs
  "source/provenance and explanation-authority boundaries distinguish evidence from entitlement to decide or speak"
  true true false

authorityStateEdge : PluralBridgeEdge
authorityStateEdge = plural-bridge-edge
  authorityCoordinate stateCoordinate recognisedBy
  "Mabo/Country/SensibLaw substrate permits recognition relations while retaining non-descent: recognition need not create antecedent authority"
  true true false

communitySocietyEdge : PluralBridgeEdge
communitySocietyEdge = plural-bridge-edge
  communityCoordinate societyCoordinate aggregatesTo
  "social-science/community projection requires scope and aggregation rather than silent promotion"
  true true false

stateSocietyEdge : PluralBridgeEdge
stateSocietyEdge = plural-bridge-edge
  stateCoordinate societyCoordinate governs
  "state/governance acts on society without identifying state and society"
  true true false

knowledgeStateConflictEdge : PluralBridgeEdge
knowledgeStateConflictEdge = plural-bridge-edge
  knowledgeCoordinate stateCoordinate conflictsWith
  "Two-Eyed, situated feminist, Mabo/Country and source-governance machinery permit disagreement between state classifications and situated knowledge"
  true true false

------------------------------------------------------------------------
-- Last-tranche operators are explicitly part of bridge admission.
------------------------------------------------------------------------

record BridgeOperatorAdmission : Set where
  constructor bridge-operator-admission
  field
    twoEyedPluralityApplied : Bool
    braidedReciprocityApplied : Bool
    intersectionalNonFactorabilityApplied : Bool
    situatedFeministKnowledgeApplied : Bool
    dialecticalRevisionAvailable : Bool
    antiLacanianDifferentGrammarAllowed : Bool
    forcedSynthesisRequired : Bool
open BridgeOperatorAdmission public

canonicalBridgeOperatorAdmission : BridgeOperatorAdmission
canonicalBridgeOperatorAdmission = bridge-operator-admission
  true true true true true true false

------------------------------------------------------------------------
-- Completion receipt for this bridge. This does not say every underlying
-- empirical/source obligation is paid; it says the parent relation architecture
-- no longer has to erase authority/provenance distinctions to connect them.
------------------------------------------------------------------------

record CountryCommunityKnowledgeAuthorityBridgeReceipt : Set where
  constructor country-community-knowledge-authority-bridge-receipt
  field
    countryCoordinatePresent : Bool
    communityCoordinatePresent : Bool
    knowledgeCoordinatePresent : Bool
    authorityCoordinatePresent : Bool
    societyCoordinatePresent : Bool
    stateCoordinatePresent : Bool
    relationRolesSeparated : Bool
    stateRecognitionNonCreative : Bool
    knowledgeNotCollapsedToScience : Bool
    communityNotCollapsedToSociety : Bool
    crossPollinationMayRetainConflict : Bool
    wikipediaCreatesAuthority : Bool
open CountryCommunityKnowledgeAuthorityBridgeReceipt public

canonicalCountryCommunityKnowledgeAuthorityBridgeReceipt :
  CountryCommunityKnowledgeAuthorityBridgeReceipt
canonicalCountryCommunityKnowledgeAuthorityBridgeReceipt =
  country-community-knowledge-authority-bridge-receipt
    true true true true true true true true true true true false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data StateRecognitionCreatesAntecedentCountryAuthority : Set where
data ScientificValidationExhaustsKnowledgeAuthority : Set where
data CommunityObservationIsSocietyObservation : Set where
data InstitutionalPowerCreatesEpistemicAuthority : Set where
data CrossPollinationErasesConflict : Set where

stateRecognitionDoesNotCreateAntecedentCountryAuthority :
  StateRecognitionCreatesAntecedentCountryAuthority → ⊥
stateRecognitionDoesNotCreateAntecedentCountryAuthority ()

scienceDoesNotExhaustKnowledgeAuthority :
  ScientificValidationExhaustsKnowledgeAuthority → ⊥
scienceDoesNotExhaustKnowledgeAuthority ()

communityDoesNotSilentlyBecomeSociety :
  CommunityObservationIsSocietyObservation → ⊥
communityDoesNotSilentlyBecomeSociety ()

institutionalPowerDoesNotCreateEpistemicAuthority :
  InstitutionalPowerCreatesEpistemicAuthority → ⊥
institutionalPowerDoesNotCreateEpistemicAuthority ()

crossPollinationMayPreserveConflict : CrossPollinationErasesConflict → ⊥
crossPollinationMayPreserveConflict ()

selectedRoadmapLeaf : Roadmap.RoadmapLeaf
selectedRoadmapLeaf = Roadmap.placeCommunityKnowledgeAuthority
