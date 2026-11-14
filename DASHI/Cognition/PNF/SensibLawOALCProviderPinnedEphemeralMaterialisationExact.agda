module DASHI.Cognition.PNF.SensibLawOALCProviderPinnedEphemeralMaterialisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawOALCPostgresPersistenceExact as Persistence
import DASHI.Law.SensibLawMaboDistributedLegalCorpusMaterialisationExact as Distributed

------------------------------------------------------------------------
-- PROVIDER-PINNED / EVICTION-SAFE SOURCE MATERIALISATION
--
-- Runtime parity target: SOURCE-MATERIALISATION-1.
--
-- The provider is allowed to be the durable possession/reacquisition lane.
-- Postgres retains immutable provider/version identity, canonical digest,
-- source-resolution and exact-span coordinates. Full canonical source bytes are
-- a lease/cache state: strict quotation/review may require them to be resident,
-- but skeleton navigation and durable provenance do not.
------------------------------------------------------------------------

data ByteResidency : Set where
  bytesResident bytesEvicted : ByteResidency

record ImmutableProviderPin : Set where
  constructor immutable-provider-pin
  field
    providerRef : String
    datasetRef : String
    datasetRevisionRef : String
    splitRef : String
    externalVersionRef : String
    sourceRef : String
    citationRef : String
    jurisdictionRef : String
    acquisitionReceiptRef : String
    immutableRevisionRequired : Bool
    immutableRevisionRequiredIsTrue : immutableRevisionRequired ≡ true

open ImmutableProviderPin public

record ProviderMaterialisationCoordinate (pin : ImmutableProviderPin) : Set where
  constructor provider-materialisation-coordinate
  field
    materialisationRef : String
    externalSourceRevisionRef : String
    documentRef : String
    canonicalDigestRef : String
    canonicalByteLengthRef : String
    residency : ByteResidency
    exactSourceResolutionPersisted : Bool
    exactSourceResolutionPersistedIsTrue : exactSourceResolutionPersisted ≡ true
    byteEvictionAllowed : Bool
    byteEvictionAllowedIsTrue : byteEvictionAllowed ≡ true
    retainFullTextByDefault : Bool
    retainFullTextByDefaultIsFalse : retainFullTextByDefault ≡ false
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open ProviderMaterialisationCoordinate public

record VerifiedRematerialisation
    (pin : ImmutableProviderPin)
    (coordinate : ProviderMaterialisationCoordinate pin) : Set where
  constructor verified-rematerialisation
  field
    observedCanonicalDigestRef : String
    observedDigestMatchesPinnedDigest :
      observedCanonicalDigestRef ≡ canonicalDigestRef coordinate
    sameProviderPinRequired : Bool
    sameProviderPinRequiredIsTrue : sameProviderPinRequired ≡ true
    silentLatestSubstitutionAllowed : Bool
    silentLatestSubstitutionAllowedIsFalse : silentLatestSubstitutionAllowed ≡ false

open VerifiedRematerialisation public

record EvictionSafeSourceBoundary : Set where
  constructor eviction-safe-source-boundary
  field
    skeletonMayNavigateWithoutResidentBytes : Bool
    skeletonMayNavigateWithoutResidentBytesIsTrue :
      skeletonMayNavigateWithoutResidentBytes ≡ true
    exactQuotationRequiresResidentVerifiedBytes : Bool
    exactQuotationRequiresResidentVerifiedBytesIsTrue :
      exactQuotationRequiresResidentVerifiedBytes ≡ true
    exactSpanDigestSurvivesByteEviction : Bool
    exactSpanDigestSurvivesByteEvictionIsTrue :
      exactSpanDigestSurvivesByteEviction ≡ true
    providerRevisionIdentitySurvivesByteEviction : Bool
    providerRevisionIdentitySurvivesByteEvictionIsTrue :
      providerRevisionIdentitySurvivesByteEviction ≡ true
    sourceResolutionReceiptSurvivesByteEviction : Bool
    sourceResolutionReceiptSurvivesByteEvictionIsTrue :
      sourceResolutionReceiptSurvivesByteEviction ≡ true
    changedDigestMayRehydrateSameCoordinate : Bool
    changedDigestMayRehydrateSameCoordinateIsFalse :
      changedDigestMayRehydrateSameCoordinate ≡ false
    cacheResidencyCreatesAuthority : Bool
    cacheResidencyCreatesAuthorityIsFalse :
      cacheResidencyCreatesAuthority ≡ false
    evictionDeletesDerivedSemanticCoordinates : Bool
    evictionDeletesDerivedSemanticCoordinatesIsFalse :
      evictionDeletesDerivedSemanticCoordinates ≡ false

open EvictionSafeSourceBoundary public

canonicalEvictionSafeSourceBoundary : EvictionSafeSourceBoundary
canonicalEvictionSafeSourceBoundary =
  eviction-safe-source-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Reuse the already-proved owners; this is a storage/runtime refinement, not a
-- second OALC persistence or legal-authority architecture.
------------------------------------------------------------------------

selectedPostgresPersistenceBoundary : Persistence.OALCPostgresPersistenceBoundary
selectedPostgresPersistenceBoundary = Persistence.canonicalOALCPostgresPersistenceBoundary

selectedDistributedLegalCorpusBoundary : Distributed.DistributedLegalCorpusBoundary
selectedDistributedLegalCorpusBoundary = Distributed.canonicalDistributedLegalCorpusBoundary

_ : Distributed.skeletonMayNavigateWithoutFullTextResident
      selectedDistributedLegalCorpusBoundary ≡ true
_ = Distributed.skeletonMayNavigateWithoutFullTextResidentIsTrue
      selectedDistributedLegalCorpusBoundary

_ : Distributed.exactQuotationRequiresExactText
      selectedDistributedLegalCorpusBoundary ≡ true
_ = Distributed.exactQuotationRequiresExactTextIsTrue
      selectedDistributedLegalCorpusBoundary

_ : Persistence.canonicalTextDuplicated selectedPostgresPersistenceBoundary ≡ false
_ = refl

_ : Persistence.persistenceCreatesAuthority selectedPostgresPersistenceBoundary ≡ false
_ = refl

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data ProviderDiscoveryImpliesResidentPossession : Set where
data MutableProviderHeadIsImmutableRevision : Set where
data ChangedDigestMayReusePinnedCoordinate : Set where
data EvictedBytesMayPayExactQuotation : Set where
data CacheResidencyCreatesLegalAuthority : Set where
data ExactSourceResolutionCreatesClaimTruth : Set where
data ByteEvictionDeletesReviewedMeaning : Set where

discoveryDoesNotImplyResidentPossession :
  ProviderDiscoveryImpliesResidentPossession → ⊥
discoveryDoesNotImplyResidentPossession ()

mutableHeadIsNotImmutableRevision : MutableProviderHeadIsImmutableRevision → ⊥
mutableHeadIsNotImmutableRevision ()

changedDigestCannotReusePinnedCoordinate : ChangedDigestMayReusePinnedCoordinate → ⊥
changedDigestCannotReusePinnedCoordinate ()

evictedBytesCannotPayExactQuotation : EvictedBytesMayPayExactQuotation → ⊥
evictedBytesCannotPayExactQuotation ()

cacheResidencyDoesNotCreateLegalAuthority : CacheResidencyCreatesLegalAuthority → ⊥
cacheResidencyDoesNotCreateLegalAuthority ()

exactResolutionDoesNotCreateClaimTruth : ExactSourceResolutionCreatesClaimTruth → ⊥
exactResolutionDoesNotCreateClaimTruth ()

byteEvictionDoesNotDeleteReviewedMeaning : ByteEvictionDeletesReviewedMeaning → ⊥
byteEvictionDoesNotDeleteReviewedMeaning ()
