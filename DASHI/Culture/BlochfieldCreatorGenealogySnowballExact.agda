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
    domainObservation : OSINT.OSINTObservation
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
-- Cross-platform same-name / handle candidates.
--
-- These are acquired because creator-outward snowballing may expose older
-- project ancestry.  They are intentionally identityUnresolved.  Same display
-- name, surname/handle fragments, thematic overlap, or chronology cannot weld
-- them to @msiyasmsi without an explicit cross-platform identity receipt.
------------------------------------------------------------------------

sameNameMediumCandidateObservation : OSINT.OSINTObservation
sameNameMediumCandidateObservation =
  OSINT.osint-observation
    "https://medium.com/@yasminanacreto/list/80f317ad2598"
    ""
    "2026-09-11 search-indexed Medium list; page reports Yasmin Anacreto, Provocations, Mar 31 2024"
    OSINT.discoveryMetadata
    OSINT.identityUnresolved
    "same-name Medium account/list candidate predating the observed @msiyasmsi X account join date"
    "cross-platform identity candidate only; does not establish same person, Blochfield ancestry, endorsement of saved material, or creator technical lineage"
    "no native cross-platform identity receipt acquired"
    true
    true
    true

crossPlatformLink3CandidateObservation : OSINT.OSINTObservation
crossPlatformLink3CandidateObservation =
  OSINT.osint-observation
    "https://link3.to/0xyasanacreto"
    ""
    "2026-09-11 search-indexed Link3 profile"
    OSINT.discoveryMetadata
    OSINT.identityUnresolved
    "0xyasanacreto.cyber profile contains featured content attributed to Yasmin Anacreto"
    "cross-platform identity candidate only; handle/name similarity and web3 context do not establish same person or Blochfield lineage"
    "no native cross-platform identity receipt acquired"
    true
    true
    true

record CrossPlatformIdentityCandidate : Set where
  constructor cross-platform-identity-candidate
  field
    candidateObservation : OSINT.OSINTObservation
    candidateLabel : String
    relationToCreator : String
    exactIdentityWeldPaid : Bool
    exactIdentityWeldPaidIsFalse : exactIdentityWeldPaid ≡ false

mediumIdentityCandidate : CrossPlatformIdentityCandidate
mediumIdentityCandidate =
  cross-platform-identity-candidate
    sameNameMediumCandidateObservation
    "Medium @yasminanacreto / Yasmin Anacreto"
    "same-name historical account candidate"
    false refl

link3IdentityCandidate : CrossPlatformIdentityCandidate
link3IdentityCandidate =
  cross-platform-identity-candidate
    crossPlatformLink3CandidateObservation
    "Link3 0xyasanacreto.cyber"
    "name/handle-context historical account candidate"
    false refl

------------------------------------------------------------------------
-- Relationship classes.  Resemblance / adjacency cannot silently become
-- ancestry or same-object lineage.
------------------------------------------------------------------------

data GenealogyRelation : Set where
  profileNamesDomain : GenealogyRelation
  profileNamesExternalConcept : GenealogyRelation
  discoveryIndexListsDomain : GenealogyRelation
  externalConceptIdentity : GenealogyRelation
  crossPlatformIdentityCandidate : GenealogyRelation
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
    edgePaid : Bool

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

mediumToCreatorIdentityCandidate : GenealogyEdge
mediumToCreatorIdentityCandidate =
  genealogy-edge
    "Medium @yasminanacreto"
    crossPlatformIdentityCandidate
    "@msiyasmsi"
    "same display name; exact identity weld not acquired"
    false

link3ToCreatorIdentityCandidate : GenealogyEdge
link3ToCreatorIdentityCandidate =
  genealogy-edge
    "Link3 0xyasanacreto.cyber"
    crossPlatformIdentityCandidate
    "@msiyasmsi"
    "name/handle-context similarity; exact identity weld not acquired"
    false

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
data SameDisplayNamePaysSamePerson : Set where
data HandleStemPaysSamePerson : Set where

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

sameDisplayNameDoesNotPaySamePerson : SameDisplayNamePaysSamePerson → ⊥
sameDisplayNameDoesNotPaySamePerson ()

handleStemDoesNotPaySamePerson : HandleStemPaysSamePerson → ⊥
handleStemDoesNotPaySamePerson ()

------------------------------------------------------------------------
-- Current creator-outward frontier.
------------------------------------------------------------------------

data GenealogyLeaf : Set where
  nativeXProfileReceipt : GenealogyLeaf
  nativeBlochfieldWebsiteContent : GenealogyLeaf
  authoritativeDomainRegistration : GenealogyLeaf
  crossPlatformIdentityWeld : GenealogyLeaf
  creatorLongFormExplanation : GenealogyLeaf
  creatorExplicitReferences : GenealogyLeaf
  externalSameObjectLineage : GenealogyLeaf

data GenealogyStanding : Set where
  genealogyPaid : GenealogyStanding
  genealogyAcquiredOutOfOrder : GenealogyStanding
  genealogyUnpaid : GenealogyStanding

genealogyStanding : GenealogyLeaf → GenealogyStanding
genealogyStanding nativeXProfileReceipt = genealogyUnpaid
genealogyStanding nativeBlochfieldWebsiteContent = genealogyUnpaid
genealogyStanding authoritativeDomainRegistration = genealogyUnpaid
genealogyStanding crossPlatformIdentityWeld = genealogyUnpaid
genealogyStanding creatorLongFormExplanation = genealogyUnpaid
genealogyStanding creatorExplicitReferences = genealogyUnpaid
genealogyStanding externalSameObjectLineage = genealogyUnpaid

-- Acquired sideways but not promoted into the ordered payment path:
--   * third-party profile -> blochfield.com association
--   * third-party 2026-08-28 domain-listing chronology candidate
--   * NASA/Q1468412 external SAA identity
--   * same-name Medium historical candidate
--   * Link3 0xyasanacreto.cyber historical candidate.
-- The next conclusion-paying leaf remains native creator material.
