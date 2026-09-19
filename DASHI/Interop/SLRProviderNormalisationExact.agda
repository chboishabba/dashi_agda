module DASHI.Interop.SLRProviderNormalisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRSharedEvidenceReducerExact as Reducer
import DASHI.Interop.SLRWikimediaFirstWorldAcquisitionExact as Wikimedia
import DASHI.Interop.SLRPostgresWorldPersistenceExact as PG
import DASHI.Interop.SLRMaboLegalIRMaterialisationExact as LegalIR

------------------------------------------------------------------------
-- SPRINT 2 M2.4 — PROVIDER NORMALISATION
--
-- Runtime target:
--   chboishabba/slr ::
--   sl-world-expansion-runtime::sprint2_provider_normalisation
--
-- Existing producer artifacts are not re-acquired here. They lower through
-- the already-paid M2.1/M2.2 canonical evidence substrate:
--
--   provider artifact
--      -> EvidenceManifestation
--      -> EvidenceSourceRevision
--      -> EvidenceSpan
--      -> EvidenceObservation
--      -> explicit review
--      -> SharedEvidenceReducer
--
-- Provider identity does not grant an alternate review or projection path.
------------------------------------------------------------------------

record ProviderNormalisationParity : Set where
  constructor providerNormalisationParity
  field
    oneCanonicalProviderCarrier : Bool
    carrierRetainsManifestation : Bool
    carrierRetainsSourceRevision : Bool
    carrierRetainsExactSpan : Bool
    carrierRetainsObservation : Bool

    wikidataUsesCanonicalCarrier : Bool
    wikipediaUsesCanonicalCarrier : Bool
    oalcUsesCanonicalCarrier : Bool
    cachedLegalUsesCanonicalCarrier : Bool

    wikidataUsesStructuredCoordinate : Bool
    wikipediaMayUseWholeRevision : Bool
    oalcMayUseWholeRevision : Bool
    cachedLegalMayUseWholeRevision : Bool

    manifestationRevisionIdentityMustMatch : Bool
    revisionDigestIdentityMustMatch : Bool
    observationRevisionMustMatchCanonicalRevision : Bool

    explicitReviewRequiredBeforeReducer : Bool
    sharedReducerUsedAfterReview : Bool
    providerSpecificReviewShortcutExists : Bool
    providerSpecificProjectionShortcutExists : Bool

    cacheFirstPathRetainedInNormalisationReceipt : Bool
    acquisitionNetworkCountRetained : Bool
    verificationNetworkCountRetained : Bool
    exactPgHitUsesZeroNetwork : Bool
    pgMissMayAcquireAndPersist : Bool
    postPersistVerificationUsesZeroNetwork : Bool
    exactSecondLookupMayReusePersistedRevision : Bool

    providerNormalisationCreatesSemanticAuthority : Bool
    providerNormalisationPromotesApplicability : Bool
    providerNormalisationPromotesClaimTruth : Bool

open ProviderNormalisationParity public

canonicalProviderNormalisationParity : ProviderNormalisationParity
canonicalProviderNormalisationParity =
  providerNormalisationParity
    true true true true true
    true true true true
    true true true true
    true true true
    true true false false
    true true true
    true true true true
    false false false

------------------------------------------------------------------------
-- Existing-owner anchors.
------------------------------------------------------------------------

sharedReducerAnchor : Reducer.SharedEvidenceReducerParity
sharedReducerAnchor = Reducer.canonicalSharedEvidenceReducerParity

wikimediaAcquisitionAnchor : Wikimedia.WikimediaFirstAcquisitionPolicy
wikimediaAcquisitionAnchor = Wikimedia.canonicalWikimediaFirstAcquisitionPolicy

postgresPersistenceAnchor : PG.PostgresWorldPersistenceBoundary
postgresPersistenceAnchor = PG.canonicalPostgresWorldPersistenceBoundary

legalIrPersistenceAnchor : LegalIR.LegalIrV2StorageParity
legalIrPersistenceAnchor = LegalIR.canonicalLegalIrV2StorageParity

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ProviderSpecificEvidenceBypassesCanonicalCarrier : Set where
data ProviderSpecificReviewBypassesCanonicalReview : Set where
data ProviderSpecificProjectionBypassesSharedReducer : Set where
data ProviderFamilyCreatesAuthority : Set where
data ProviderFamilyPromotesApplicability : Set where
data ProviderFamilyPromotesClaimTruth : Set where
data ExactPgHitRequiresNetwork : Set where
data PersistedSourceRequiresReacquisition : Set where
data WikidataStructuredCoordinateRequiresFakeTextSpan : Set where

providerSpecificEvidenceCannotBypassCanonicalCarrier :
  ProviderSpecificEvidenceBypassesCanonicalCarrier → ⊥
providerSpecificEvidenceCannotBypassCanonicalCarrier ()

providerSpecificReviewCannotBypassCanonicalReview :
  ProviderSpecificReviewBypassesCanonicalReview → ⊥
providerSpecificReviewCannotBypassCanonicalReview ()

providerSpecificProjectionCannotBypassSharedReducer :
  ProviderSpecificProjectionBypassesSharedReducer → ⊥
providerSpecificProjectionCannotBypassSharedReducer ()

providerFamilyDoesNotCreateAuthority : ProviderFamilyCreatesAuthority → ⊥
providerFamilyDoesNotCreateAuthority ()

providerFamilyDoesNotPromoteApplicability : ProviderFamilyPromotesApplicability → ⊥
providerFamilyDoesNotPromoteApplicability ()

providerFamilyDoesNotPromoteClaimTruth : ProviderFamilyPromotesClaimTruth → ⊥
providerFamilyDoesNotPromoteClaimTruth ()

exactPgHitDoesNotRequireNetwork : ExactPgHitRequiresNetwork → ⊥
exactPgHitDoesNotRequireNetwork ()

persistedSourceDoesNotRequireReacquisition : PersistedSourceRequiresReacquisition → ⊥
persistedSourceDoesNotRequireReacquisition ()

wikidataStructuredCoordinateDoesNotRequireFakeTextSpan :
  WikidataStructuredCoordinateRequiresFakeTextSpan → ⊥
wikidataStructuredCoordinateDoesNotRequireFakeTextSpan ()
