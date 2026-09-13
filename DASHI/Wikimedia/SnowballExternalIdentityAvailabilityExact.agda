module DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Wikimedia.ScientificReferenceEntityAtlasExact as Entity
import DASHI.Wikimedia.NativeReferenceAttributedSourceBridgeExact as NativeBridge

------------------------------------------------------------------------
-- SNOWBALL EXTERNAL-IDENTITY AVAILABILITY
--
-- External identity is acquired opportunistically when applicable and
-- available.  QID / DOI / arXiv / canonical URL / official identifiers are
-- provenance coordinates, not semantic authority.  Failure to resolve one is
-- retained explicitly and normally does not block a domain theorem.
------------------------------------------------------------------------

data ExternalIdentityKind : Set where
  wikidataQid canonicalURL doi arxiv officialIdentifier wikimediaReferenceUrl :
    ExternalIdentityKind

data IdentityResolution : Set where
  notApplicable : String → IdentityResolution
  unresolved : String → IdentityResolution
  candidate : String → String → IdentityResolution
  verified : String → String → IdentityResolution

record ExternalIdentityDemand : Set where
  constructor external-identity-demand
  field
    consumerReference : String
    queryReference : String
    subjectLabel : String
    identityKind : ExternalIdentityKind
    resolution : IdentityResolution
    relevantToAttribution : Bool
    blocksDomainProofWhenUnresolved : Bool
    externalIdentityCreatesAuthority : Bool
open ExternalIdentityDemand public

mkOptionalIdentityDemand :
  String → String → String → ExternalIdentityKind → IdentityResolution →
  ExternalIdentityDemand
mkOptionalIdentityDemand consumer query subject kind status =
  external-identity-demand consumer query subject kind status true false false

------------------------------------------------------------------------
-- Policy: ask when applicable/available, retain unresolved explicitly.
------------------------------------------------------------------------

record SnowballExternalIdentityPolicy : Set where
  constructor snowball-external-identity-policy
  field
    requestStableIdentityWhenApplicable : Bool
    requestCanonicalLinkWhenApplicable : Bool
    verifiedIdentityMustBeRetainedWhenRelevant : Bool
    unresolvedIdentityRemainsExplicit : Bool
    unresolvedIdentityIsNegativeEvidence : Bool
    unresolvedIdentityBlocksUnrelatedDomainProof : Bool
    qidReplacesPublicationIdentifier : Bool
    externalIdentityCreatesSemanticAuthority : Bool
open SnowballExternalIdentityPolicy public

canonicalExternalIdentityPolicy : SnowballExternalIdentityPolicy
canonicalExternalIdentityPolicy =
  snowball-external-identity-policy
    true true true true false false false false

------------------------------------------------------------------------
-- Existing repository instances.
------------------------------------------------------------------------

qidResolutionAlreadySupportsUnresolved : Bool
qidResolutionAlreadySupportsUnresolved = true

attributionSnowballAlreadyRetainsIdentityAxes : Bool
attributionSnowballAlreadyRetainsIdentityAxes =
  AttributionSnowball.AttributionSnowballBoundary.attributionInstantiatesPluralLens
    AttributionSnowball.canonicalAttributionSnowballBoundary

record AttributedIdentityBundle (source : Attribution.AttributedSource) : Set where
  constructor attributed-identity-bundle
  field
    sourceRoleReceipt : AttributionSnowball.SourceRoleSnowballReceipt source
    entityIdentity : Entity.ScientificReferenceEntity
    sameSubjectReceipt : Set
    canonicalReferenceInspected : Set
    qidIsSupplementalIdentity : Bool
    bibliographicIdentifierRetained : Bool
open AttributedIdentityBundle public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data UnresolvedQidMeansEntityAbsent : Set where
data QidPaysSourceTruth : Set where
data P854CandidateEqualsVerifiedCanonicalSource : Set where
data OptionalIdentityFailureBlocksEveryConsumer : Set where
data VerifiedRelevantIdentityMayBeSilentlyDropped : Set where

unresolvedQidIsNotEntityAbsence : UnresolvedQidMeansEntityAbsent → ⊥
unresolvedQidIsNotEntityAbsence ()

qidDoesNotPaySourceTruth : QidPaysSourceTruth → ⊥
qidDoesNotPaySourceTruth ()

p854CandidateStillNeedsInspection : P854CandidateEqualsVerifiedCanonicalSource → ⊥
p854CandidateStillNeedsInspection ()

optionalIdentityFailureIsConsumerIndexed : OptionalIdentityFailureBlocksEveryConsumer → ⊥
optionalIdentityFailureIsConsumerIndexed ()

verifiedRelevantIdentityMustSnowball : VerifiedRelevantIdentityMayBeSilentlyDropped → ⊥
verifiedRelevantIdentityMustSnowball ()

nativeReferenceBoundaryRetained :
  NativeBridge.NativeReferenceAttributedSourceBoundary
nativeReferenceBoundaryRetained = NativeBridge.canonicalNativeReferenceAttributedSourceBoundary
