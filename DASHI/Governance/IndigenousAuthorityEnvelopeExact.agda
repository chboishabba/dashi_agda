module DASHI.Governance.IndigenousAuthorityEnvelopeExact where

open import DASHI.Core.Prelude
import DASHI.Core.SituatedClaimAuthoritySystemExact as Situated
import DASHI.Governance.IndigenousAuthoritySourceRegistryExact as Sources

------------------------------------------------------------------------
-- INDIGENOUS AUTHORITY ENVELOPE
--
-- CARE / OCAP® / Local Contexts motivate different coordinates.  This module
-- deliberately refuses to flatten provenance, governance, protocol,
-- permission and sovereignty into one source-origin enum.
------------------------------------------------------------------------

data ProvenanceRole : Set where
  communityOrigin communityCoAuthorship institutionalCustodianship externalDescription : ProvenanceRole

data GovernanceRole : Set where
  communityControlled sharedGovernance externalGovernance : GovernanceRole

data ProtocolRole : Set where
  protocolSpecified protocolUnspecified : ProtocolRole

data PermissionRole : Set where
  studyPermitted collaborationPermitted interventionPermitted permissionUnspecified : PermissionRole

data SovereignStanding : Set where
  originatingAuthority externalObserverStanding : SovereignStanding

record AuthorityEnvelope : Set where
  constructor authorityEnvelope
  field
    provenance : ProvenanceRole
    governance : GovernanceRole
    protocol : ProtocolRole
    permission : PermissionRole
    sovereignStanding : SovereignStanding

communityResearchEnvelope : AuthorityEnvelope
communityResearchEnvelope =
  authorityEnvelope communityOrigin communityControlled protocolSpecified collaborationPermitted originatingAuthority

externalPublishedDescription : AuthorityEnvelope
externalPublishedDescription =
  authorityEnvelope externalDescription externalGovernance protocolUnspecified permissionUnspecified externalObserverStanding

provenanceIdentityDoesNotDeterminePermission :
  {left right : AuthorityEnvelope} →
  AuthorityEnvelope.provenance left ≡ AuthorityEnvelope.provenance right →
  AuthorityEnvelope.permission left ≡ AuthorityEnvelope.permission right → Set
provenanceIdentityDoesNotDeterminePermission _ _ = ⊤

externalDescriptionIsNotOriginatingAuthority :
  AuthorityEnvelope.sovereignStanding externalPublishedDescription ≡ originatingAuthority → ⊥
externalDescriptionIsNotOriginatingAuthority ()

externalPublicationDoesNotCreatePermission :
  AuthorityEnvelope.permission externalPublishedDescription ≡ studyPermitted → ⊥
externalPublicationDoesNotCreatePermission ()

correctProvenanceDoesNotTransferSovereignty :
  AuthorityEnvelope.sovereignStanding communityResearchEnvelope ≡ externalObserverStanding → ⊥
correctProvenanceDoesNotTransferSovereignty ()

-- Source receipts are present for attribution, not theorem authorship.
careSource : Sources.SourceReference
careSource = Sources.care2020

ocapSource : Sources.SourceReference
ocapSource = Sources.ocapFNIGC

localContextsSource : Sources.SourceReference
localContextsSource = Sources.localContextsTK

record IndigenousAuthorityEnvelopeBoundary : Set where
  constructor indigenousAuthorityEnvelopeBoundary
  field
    provenanceEqualsPermission : Bool
    provenanceEqualsPermissionIsFalse : provenanceEqualsPermission ≡ false
    accessEqualsAuthority : Bool
    accessEqualsAuthorityIsFalse : accessEqualsAuthority ≡ false
    publicationMeansOpenReuse : Bool
    publicationMeansOpenReuseIsFalse : publicationMeansOpenReuse ≡ false
    attributionMeansConsentForReinterpretation : Bool
    attributionMeansConsentForReinterpretationIsFalse :
      attributionMeansConsentForReinterpretation ≡ false
    authorizedUseTransfersSovereignty : Bool
    authorizedUseTransfersSovereigntyIsFalse : authorizedUseTransfersSovereignty ≡ false

canonicalIndigenousAuthorityEnvelopeBoundary : IndigenousAuthorityEnvelopeBoundary
canonicalIndigenousAuthorityEnvelopeBoundary =
  indigenousAuthorityEnvelopeBoundary false refl false refl false refl false refl false refl
