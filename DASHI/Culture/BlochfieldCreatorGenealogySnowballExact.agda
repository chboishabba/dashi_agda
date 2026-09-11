module DASHI.Culture.BlochfieldCreatorGenealogySnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballOSINTAcquisitionInvariantExact as OSINT
import DASHI.Culture.BoundaryConservativeTransfigurationBlochfieldExact as Boundary

------------------------------------------------------------------------
-- BLOCHFIELD CREATOR-OUTWARD SOURCE GENEALOGY
--
-- This is an acquisition/same-object ledger, not a theory generator.
-- The highest-alpha route is creator-outward:
--
--   @msiyasmsi profile
--     -> creator-linked blochfield.com
--     -> creator profile's "South Atlantic Geomag. Anomaly" descriptor
--     -> native website / long-form objects
--     -> explicit references
--     -> external lineage.
--
-- Acquisition may occur out of dependency order.  Promotion/payment may not
-- skip native-carrier, identity, provenance, or same-object obligations.
------------------------------------------------------------------------

creatorProfileObservation : OSINT.OSINTObservation
creatorProfileObservation =
  OSINT.osint-observation
    "https://x.com/msiyasmsi"
    "https://w.twstalker.com/msiyasmsi"
    "2026-09-11 search-indexed third-party X profile mirror"
    OSINT.tertiaryAggregation
    OSINT.identityUnresolved
    "profile mirror for @msiyasmsi displays Yasmin Anacreto and includes blochfield.com plus South Atlantic Geomag. Anomaly in the profile description"
    "creator/project discovery coordinate only; mirror does not pay native X profile identity, website ownership, technical authorship, or theory lineage"
    "no native X profile digest acquired"
    false
    true
    true

record CreatorProfileProjectAssociation : Set where
  constructor creator-profile-project-association
  field
    observation : OSINT.OSINTObservation
    displayNameReported : String
    handle : String
    joinedReported : String
    linkedProjectDomain : String
    profileProjectDescriptor : String
    sourceBound : Bool
    sourceBoundIsTrue : sourceBound ≡ true
    nativeProfilePaid : Bool
    nativeProfilePaidIsFalse : nativeProfilePaid ≡ false

creatorProfileProjectAssociation : CreatorProfileProjectAssociation
creatorProfileProjectAssociation =
  creator-profile-project-association
    creatorProfileObservation
    "Yasmin Anacreto"
    "@msiyasmsi"
    "Joined November 2024"
    "blochfield.com"
    "South Atlantic Geomag. Anomaly"
    true refl
    false refl

------------------------------------------------------------------------
-- Domain chronology discovery.
--
-- A public new-domain index places blochfield.com in its list for 2026-08-28.
-- This is retained as discovery metadata only.  It is not authoritative RDAP /
-- WHOIS custody and does not prove registrant identity or creator ownership.
------------------------------------------------------------------------

domainListingObservation : OSINT.OSINTObservation
domainListingObservation =
  OSINT.osint-observation
    "https://com.all-url.info/12/21/"
    ""
    "2026-09-11 retrieval of New .COM Domains for 2026-08-28, page 22"
    OSINT.discoveryMetadata
    OSINT.identityUnresolved
    "blochfield.com appears in a third-party list of new .COM domains for 2026-08-28"
    "chronology/search lead only; does not establish registrar truth, registrant identity, creator ownership, publication date, or website content"
    "no registrar/RDAP digest acquired"
    false
    true
    true

record DomainChronologyCandidate : Set where
  constructor domain-chronology-candidate
  field
    observation : OSINT.OSINTObservation
    domain : String
    listedDate : String
    role : String
    authoritativeRegistrationReceipt : Bool
    authoritativeRegistrationReceiptIsFalse :
      authoritativeRegistrationReceipt ≡ false

blochfieldDomainChronologyCandidate : DomainChronologyCandidate
blochfieldDomainChronologyCandidate =
  domain-chronology-candidate
    domainListingObservation
    "blochfield.com"
    "2026-08-28"
    "third-party registration/appearance chronology candidate"
    false refl

------------------------------------------------------------------------
-- Independent external concept anchor: South Atlantic Anomaly.
--
-- This pays only the external identity/fact that the SAA is a real geomagnetic
-- anomaly studied by NASA.  It does NOT pay the creator's intended relation
-- between Blochfield and the SAA, nor any mathematics/physics of Blochfield.
------------------------------------------------------------------------

southAtlanticAnomalyNASASource : Attribution.AttributedSource
southAtlanticAnomalyNASASource =
  Attribution.mkNoDOISource
    "NASA"
    "NASA Researchers Track Slowly Splitting 'Dent' in Earth's Magnetic Field"
    "NASA / Goddard Space Flight Center"
    "2020"
    "https://www.nasa.gov/missions/icon/nasa-researchers-track-slowly-splitting-dent-in-earths-magnetic-field/"
    Attribution.institutionalSource
    "External physical-concept anchor for the South Atlantic Anomaly only; not evidence of Blochfield theory lineage or creator technical claims."
    Attribution.publicAttribution

southAtlanticAnomalyQID : String
southAtlanticAnomalyQID = "Q1468412"

southAtlanticAnomalyDewey : String
southAtlanticAnomalyDewey = "unresolved"

southAtlanticAnomalyDOI : String
southAtlanticAnomalyDOI = "no DOI claimed for the inspected NASA web source"

------------------------------------------------------------------------
-- Relationship classes.  Resemblance / adjacency cannot silently become
-- ancestry or same-object lineage.
------------------------------------------------------------------------

data GenealogyRelation : Set where
  profileNamesDomain : GenealogyRelation
  profileNamesExternalConcept : GenealogyRelation
  discoveryIndexListsDomain : GenealogyRelation
  externalConceptIdentity : GenealogyRelation
  creatorCitesSource : GenealogyRelation
  derivedFromSource : GenealogyRelation
  sameObjectTechnicalLineage : GenealogyRelation

record GenealogyEdge : Set where
  constructor genealogy-edge
  field
    fromObject : String
    relation : GenealogyRelation
    toObject : String
    evidenceReference : String
    paid : Bool

creatorProfileToDomain : GenealogyEdge
creatorProfileToDomain =
  genealogy-edge
    "@msiyasmsi profile mirror"
    profileNamesDomain
    "blochfield.com"
    "2026-09-11 third-party profile mirror"
    true

creatorProfileToSAA : GenealogyEdge
creatorProfileToSAA =
  genealogy-edge
    "@msiyasmsi profile mirror"
    profileNamesExternalConcept
    "South Atlantic Anomaly / Q1468412"
    "profile text: South Atlantic Geomag. Anomaly"
    true

nasaToSAAIdentity : GenealogyEdge
nasaToSAAIdentity =
  genealogy-edge
    "NASA South Atlantic Anomaly source"
    externalConceptIdentity
    "South Atlantic Anomaly / Q1468412"
    "NASA institutional source plus Wikidata semantic identity coordinate"
    true

blochfieldSameObjectTechnicalLineage : GenealogyEdge
blochfieldSameObjectTechnicalLineage =
  genealogy-edge
    "Blochfield creator objects"
    sameObjectTechnicalLineage
    "independent technical literature"
    "no creator citation / derivation / same-object receipt acquired"
    false

sameObjectTechnicalLineageStillUnpaid : Boundary.LeafStanding
sameObjectTechnicalLineageStillUnpaid =
  Boundary.blochfieldSnowballStanding Boundary.externalSameObjectTheoryLineage

creatorLongFormStillUnpaid : Boundary.LeafStanding
creatorLongFormStillUnpaid =
  Boundary.blochfieldSnowballStanding Boundary.creatorLongFormIdentity

------------------------------------------------------------------------
-- Non-promotion / WrongType firewalls.
------------------------------------------------------------------------

data CreatorProfileLinkPaysNativeWebsite : Set where
data DomainListingProvesCreatorOwnership : Set where
data SouthAtlanticAnomalyPaysBlochfieldTheoryLineage : Set where
data ExternalConceptAdjacencyCreatesDerivation : Set where

data SearchIndexedProfileEqualsNativeProfile : Set where

creatorProfileLinkDoesNotPayNativeWebsite :
  CreatorProfileLinkPaysNativeWebsite → ⊥
creatorProfileLinkDoesNotPayNativeWebsite ()

domainListingDoesNotProveCreatorOwnership :
  DomainListingProvesCreatorOwnership → ⊥
domainListingDoesNotProveCreatorOwnership ()

southAtlanticAnomalyDoesNotPayBlochfieldTheoryLineage :
  SouthAtlanticAnomalyPaysBlochfieldTheoryLineage → ⊥
southAtlanticAnomalyDoesNotPayBlochfieldTheoryLineage ()

externalConceptAdjacencyDoesNotCreateDerivation :
  ExternalConceptAdjacencyCreatesDerivation → ⊥
externalConceptAdjacencyDoesNotCreateDerivation ()

searchIndexedProfileDoesNotEqualNativeProfile :
  SearchIndexedProfileEqualsNativeProfile → ⊥
searchIndexedProfileDoesNotEqualNativeProfile ()

------------------------------------------------------------------------
-- Current creator-outward frontier.
------------------------------------------------------------------------

data GenealogyLeaf : Set where
  nativeXProfileReceipt : GenealogyLeaf
  nativeBlochfieldWebsiteContent : GenealogyLeaf
  authoritativeDomainRegistration : GenealogyLeaf
  creatorLongFormExplanation : GenealogyLeaf
  creatorExplicitReferences : GenealogyLeaf
  externalSameObjectLineage : GenealogyLeaf

data GenealogyStanding : Set where
  paid : GenealogyStanding
  acquiredOutOfOrder : GenealogyStanding
  unpaid : GenealogyStanding

genealogyStanding : GenealogyLeaf → GenealogyStanding
genealogyStanding nativeXProfileReceipt = unpaid
genealogyStanding nativeBlochfieldWebsiteContent = unpaid
genealogyStanding authoritativeDomainRegistration = unpaid
genealogyStanding creatorLongFormExplanation = unpaid
genealogyStanding creatorExplicitReferences = unpaid
genealogyStanding externalSameObjectLineage = unpaid

-- Acquired sideways but not promoted into the ordered payment path:
--   * third-party profile -> blochfield.com association
--   * third-party 2026-08-28 domain-listing chronology candidate
--   * NASA/Q1468412 external SAA identity.
-- The next conclusion-paying leaf remains native creator material.
