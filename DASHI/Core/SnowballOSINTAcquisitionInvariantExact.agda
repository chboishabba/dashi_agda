module DASHI.Core.SnowballOSINTAcquisitionInvariantExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- OSINT AS A SNOWBALL ACQUISITION MODE
--
-- OSINT changes the acquisition route, not the evidentiary standard.
-- Publicly observable artifacts may accumulate opportunistically with exact
-- provenance, source role, identity status and proposition scope retained.
-- Observation, identity, support, authority, corroboration and downstream
-- inference are separate consumer-relative coordinates.
------------------------------------------------------------------------

data OSINTSourceClass : Set where
  publicPrimaryRecord : OSINTSourceClass
  publicInstitutionalStatement : OSINTSourceClass
  publicFirstPersonStatement : OSINTSourceClass
  archivedPublicArtifact : OSINTSourceClass
  secondaryReporting : OSINTSourceClass
  tertiaryAggregation : OSINTSourceClass
  discoveryMetadata : OSINTSourceClass

data OSINTCarrierIdentity : Set where
  exactNativeCarrier : OSINTCarrierIdentity
  authenticatedMirror : OSINTCarrierIdentity
  sameSourceAlternateLocator : OSINTCarrierIdentity
  sourceOfSourceCarrier : OSINTCarrierIdentity
  siblingSourceCarrier : OSINTCarrierIdentity
  identityUnresolved : OSINTCarrierIdentity

data CorroborationIndependence : Set where
  sameOriginRepublication : CorroborationIndependence
  independentOrigin : CorroborationIndependence
  independenceUnresolved : CorroborationIndependence

record OSINTObservation : Set where
  constructor osint-observation
  field
    locator : String
    archiveOrMirrorLocator : String
    retrievalReference : String
    sourceClass : OSINTSourceClass
    carrierIdentity : OSINTCarrierIdentity
    propositionReference : String
    propositionScope : String
    contentDigestReference : String
    nativeMetadataAvailable : Bool
    sourceRoleRetained : Bool
    publicLawfulAcquisition : Bool

open OSINTObservation public

record OSINTAdmissionReceipt (observation : OSINTObservation) : Set where
  constructor osint-admission-receipt
  field
    observationIdentityChecked : Bool
    propositionScopeChecked : Bool
    sourceRoleChecked : Bool
    corroborationIndependenceChecked : Bool
    propositionSupportPaid : Bool
    domainAuthorityPaid : Bool
    downstreamConclusionPaid : Bool
    promotionStillReauditable : Bool

open OSINTAdmissionReceipt public

record OSINTCorroborationReceipt : Set where
  constructor osint-corroboration-receipt
  field
    firstObservationReference : String
    secondObservationReference : String
    independence : CorroborationIndependence
    sameOriginCountedAsIndependent : Bool
    corroboratedPropositionReference : String
    corroborationCreatesAuthority : Bool

open OSINTCorroborationReceipt public

------------------------------------------------------------------------
-- Non-collapse rules.
------------------------------------------------------------------------

data PublicAvailabilityCreatesTruth : Set where
data SearchRankCreatesSupport : Set where
data SearchSnippetCreatesSupport : Set where
data MultipleRepublicationsCreateIndependentCorroboration : Set where
data SourceOfSourceEqualsSameSource : Set where
data ArchiveMirrorAutomaticallyEqualsNativeCarrier : Set where
data SearchNonLocationMeansKnownAbsence : Set where
data OSINTObservationCreatesCulpritInference : Set where

data OSINTObservationCreatesCauseOfDeath : Set where

publicAvailabilityDoesNotCreateTruth : PublicAvailabilityCreatesTruth → ⊥
publicAvailabilityDoesNotCreateTruth ()

searchRankDoesNotCreateSupport : SearchRankCreatesSupport → ⊥
searchRankDoesNotCreateSupport ()

searchSnippetDoesNotCreateSupport : SearchSnippetCreatesSupport → ⊥
searchSnippetDoesNotCreateSupport ()

republicationDoesNotCreateIndependentCorroboration :
  MultipleRepublicationsCreateIndependentCorroboration → ⊥
republicationDoesNotCreateIndependentCorroboration ()

sourceOfSourceIsNotSameSource : SourceOfSourceEqualsSameSource → ⊥
sourceOfSourceIsNotSameSource ()

archiveMirrorNeedsIdentityReceipt : ArchiveMirrorAutomaticallyEqualsNativeCarrier → ⊥
archiveMirrorNeedsIdentityReceipt ()

searchFailureDoesNotCreateKnownAbsence : SearchNonLocationMeansKnownAbsence → ⊥
searchFailureDoesNotCreateKnownAbsence ()

osintObservationDoesNotCreateCulprit : OSINTObservationCreatesCulpritInference → ⊥
osintObservationDoesNotCreateCulprit ()

osintObservationDoesNotCreateCauseOfDeath : OSINTObservationCreatesCauseOfDeath → ⊥
osintObservationDoesNotCreateCauseOfDeath ()

record OSINTSnowballBoundary : Set where
  constructor osint-snowball-boundary
  field
    osintChangesAcquisitionRouteNotTruthStandard : Bool
    publicArtifactsMayAccumulateOutOfOrder : Bool
    sourceRoleAndIdentityMustRemainRetained : Bool
    providerRankOrSnippetMayPaySupport : Bool
    sourceOfSourceMayRefineSearch : Bool
    sourceOfSourceEqualsExactCarrier : Bool
    republicationEqualsIndependentCorroboration : Bool
    publicNonLocationEqualsKnownAbsence : Bool
    osintMayBypassLawfulAccessConstraints : Bool
    observationAutomaticallyCreatesDownstreamConclusion : Bool

open OSINTSnowballBoundary public

canonicalOSINTSnowballBoundary : OSINTSnowballBoundary
canonicalOSINTSnowballBoundary =
  osint-snowball-boundary
    true true true false true false false false false false
