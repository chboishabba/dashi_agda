module DASHI.Culture.Preservation.ControlledDisclosureCore where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- Preservation-first controlled disclosure.
--
-- The authoritative archive may be semantically complete while each public
-- view is intentionally lossy.  This core is a compact policy surface, not a
-- claim that encryption, custody, consent, or safe publication are solved.
------------------------------------------------------------------------

data DisclosureLevel : Set where
  publicDisclosure : DisclosureLevel
  attributedSummaryDisclosure : DisclosureLevel
  controlledAccessDisclosure : DisclosureLevel
  communityControlledDisclosure : DisclosureLevel
  existenceOnlyDisclosure : DisclosureLevel
  locationRedactedDisclosure : DisclosureLevel
  nonDisclosable : DisclosureLevel

data PreservationEnvelope : Set where
  publicReproducibleEnvelope : PreservationEnvelope
  publicSummaryPrivateSourcesEnvelope : PreservationEnvelope
  embargoedEnvelope : PreservationEnvelope
  communityControlledEnvelope : PreservationEnvelope
  multiPartyControlledEnvelope : PreservationEnvelope
  existenceOnlyPublicEnvelope : PreservationEnvelope
  successionRestrictedEnvelope : PreservationEnvelope
  sacredNonExportableEnvelope : PreservationEnvelope

data DisclosureAction : Set where
  retainAction : DisclosureAction
  removeAction : DisclosureAction
  pseudonymiseAction : DisclosureAction
  coarsenLocationAction : DisclosureAction
  aggregateAction : DisclosureAction
  existenceClaimAction : DisclosureAction
  controlledSummaryAction : DisclosureAction
  delayedDisclosureAction : DisclosureAction
  authorisationRequiredAction : DisclosureAction

data KnowledgeSurface : Set where
  claimSurface : KnowledgeSurface
  attributionSurface : KnowledgeSurface
  locationSurface : KnowledgeSurface
  processParameterSurface : KnowledgeSurface
  ritualSurface : KnowledgeSurface
  ecologicalSurface : KnowledgeSurface
  contactSurface : KnowledgeSurface
  buildMetadataSurface : KnowledgeSurface
  namedKnowledgeSurface : String → KnowledgeSurface

record DisclosureRule : Set where
  constructor disclosureRule
  field
    targetSurface : KnowledgeSurface
    action : DisclosureAction
    authorityLabel : String
    ruleReading : String

open DisclosureRule public

record FullArchive (Claim : Set) : Set₁ where
  constructor fullArchive
  field
    archiveLabel : String
    archivedClaims : List Claim
    sourceAtlas : Source.AttributedSourceAtlas
    dependencyLock : String
    validationCommand : String
    preservationEnvelope : PreservationEnvelope
    governanceReading : String

open FullArchive public

record PublicClaimProjection (Claim : Set) : Set₁ where
  constructor publicClaimProjection
  field
    sourceClaim : Claim
    publicClaim : Claim
    appliedAction : DisclosureAction
    projectionReading : String

open PublicClaimProjection public

record SourceDisclosureProjection : Set where
  constructor sourceDisclosureProjection
  field
    attributedSource : Source.AttributedSource
    attributionProjection : Source.AttributionProjection attributedSource
    sourceDisclosureLevel : DisclosureLevel

open SourceDisclosureProjection public

record PublicArtifact (Claim : Set) : Set₁ where
  constructor publicArtifact
  field
    publicLabel : String
    claimProjections : List (PublicClaimProjection Claim)
    sourceProjections : List SourceDisclosureProjection
    withheldResidual : String
    disclosureLevel : DisclosureLevel

open PublicArtifact public

record ProjectionPolicy (Claim : Set) : Set₁ where
  constructor projectionPolicy
  field
    policyLabel : String
    rules : List DisclosureRule
    buildProjection : FullArchive Claim → PublicArtifact Claim
    policyAuthority : String
    policyReading : String

open ProjectionPolicy public

record PublicationReceipt
    {Claim : Set}
    (archive : FullArchive Claim)
    (policy : ProjectionPolicy Claim)
    (artifact : PublicArtifact Claim) : Set₁ where
  constructor publicationReceipt
  field
    generatedByPolicy :
      artifact ≡ buildProjection policy archive
    attributionClassified : Bool
    attributionClassifiedIsTrue : attributionClassified ≡ true
    restrictedContentAbsentByConstruction : Bool
    restrictedContentAbsentByConstructionIsTrue :
      restrictedContentAbsentByConstruction ≡ true
    metadataAudited : Bool
    metadataAuditedIsTrue : metadataAudited ≡ true
    receiptReading : String

open PublicationReceipt public

data PreservationPublicationDistinction : Set where
  archivedDoesNotImplyPublic : PreservationPublicationDistinction
  restrictedDoesNotImplyWeaklyPreserved : PreservationPublicationDistinction
  publicViewDoesNotImplyCompleteRepresentation : PreservationPublicationDistinction
  integrityDoesNotImplyContentDisclosure : PreservationPublicationDistinction
  formalisableDoesNotImplyPubliclyRenderAble : PreservationPublicationDistinction

record PreservationPublicationBoundary : Set where
  constructor preservationPublicationBoundary
  field
    distinctions : List PreservationPublicationDistinction
    maximalArchiveClaim : Bool
    maximalArchiveClaimIsFalse : maximalArchiveClaim ≡ false
    automaticPublicationClaim : Bool
    automaticPublicationClaimIsFalse : automaticPublicationClaim ≡ false
    completeNonLeakageClaim : Bool
    completeNonLeakageClaimIsFalse : completeNonLeakageClaim ≡ false
    boundaryReading : String

open PreservationPublicationBoundary public

canonicalPreservationPublicationBoundary : PreservationPublicationBoundary
canonicalPreservationPublicationBoundary =
  preservationPublicationBoundary
    ( archivedDoesNotImplyPublic
    ∷ restrictedDoesNotImplyWeaklyPreserved
    ∷ publicViewDoesNotImplyCompleteRepresentation
    ∷ integrityDoesNotImplyContentDisclosure
    ∷ formalisableDoesNotImplyPubliclyRenderAble
    ∷ [] )
    false
    refl
    false
    refl
    false
    refl
    "Preservation completeness and public accessibility are separate governed surfaces; this boundary records the distinction without claiming a complete archival or non-leakage implementation."

canonicalControlledDisclosureReceipt : GenericReceipt.GenericReceipt
canonicalControlledDisclosureReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "preservation-first controlled disclosure core"
    "DASHI.Culture.Preservation.ControlledDisclosureCore"
    "FullArchive / ProjectionPolicy / PublicArtifact / PublicationReceipt"
    "separates semantically reconstructible preservation from typed, attribution-aware public projections"
    "the core does not claim consent, secure custody, cryptographic durability, complete non-leakage, or authority to acquire or disclose restricted knowledge"
    "agda -i . DASHI/Culture/Preservation/ControlledDisclosureCore.agda"
