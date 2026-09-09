module DASHI.Cognition.PNF.SensibLawOALCPostgresCacheFirstResolutionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawOALCLegislationParserInputContractExact as OALC
import DASHI.Cognition.PNF.SensibLawOALCPostgresPersistenceExact as PG

------------------------------------------------------------------------
-- CACHE-FIRST OALC / POSTGRES RESOLUTION
--
-- Exact runtime parity target for sensiblaw-pg-source-store/cache_first.rs.
-- PostgreSQL is checked before governed acquisition.  Only an exact retained
-- LegalFollow demand receipt is a cache hit.  A miss schedules acquisition;
-- it is never negative source/legal evidence.
------------------------------------------------------------------------

record ExactCacheLookupDemand : Set where
  constructor exact-cache-lookup-demand
  field
    legalFollowDemandRef : String
    citationRef : String
    jurisdictionRef : String
    sourceRoleRef : String
    authorityLevelRef : String
    temporalRef : String

open ExactCacheLookupDemand public

record ExactPersistedCacheHit
    (demand : ExactCacheLookupDemand) : Set where
  constructor exact-persisted-cache-hit
  field
    documentRef : String
    externalSourceRevisionRef : String
    sourceResolutionRef : String
    exactDemandMatch : Bool
    citationMatch : Bool
    jurisdictionMatch : Bool
    sourceRoleMatch : Bool
    authorityLevelMatch : Bool
    temporalMatch : Bool
    canonicalTextRef : String

open ExactPersistedCacheHit public

record CacheHitAdmission
    {demand : ExactCacheLookupDemand}
    (hit : ExactPersistedCacheHit demand) : Set where
  constructor cache-hit-admission
  field
    exactDemandPaid : exactDemandMatch hit ≡ true
    citationPaid : citationMatch hit ≡ true
    jurisdictionPaid : jurisdictionMatch hit ≡ true
    sourceRolePaid : sourceRoleMatch hit ≡ true
    authorityLevelPaid : authorityLevelMatch hit ≡ true
    temporalPaid : temporalMatch hit ≡ true

open CacheHitAdmission public

data CacheLookupState (demand : ExactCacheLookupDemand) : Set where
  exactPGHit :
    (hit : ExactPersistedCacheHit demand) →
    CacheHitAdmission hit →
    CacheLookupState demand
  pgMiss : CacheLookupState demand
  malformedCachedRow : String → CacheLookupState demand
  databaseUnavailable : String → CacheLookupState demand

record GovernedAcquisitionReceipt
    (demand : ExactCacheLookupDemand) : Set where
  constructor governed-acquisition-receipt
  field
    providerRef : String
    resolverRef : String
    datasetRevisionRef : String
    externalVersionRef : String
    exactDemandMatch : Bool
    networkRequests : Nat
    receiptAuthorityRef : String

open GovernedAcquisitionReceipt public

record PersistAfterAcquireReceipt
    {demand : ExactCacheLookupDemand}
    (acquisition : GovernedAcquisitionReceipt demand) : Set where
  constructor persist-after-acquire-receipt
  field
    persistedRevisionRef : String
    persistedResolutionRef : String
    postPersistHit : ExactPersistedCacheHit demand
    postPersistAdmission : CacheHitAdmission postPersistHit

open PersistAfterAcquireReceipt public

data CacheFirstResolution
    (demand : ExactCacheLookupDemand) : Set where
  resolvedFromPG :
    (hit : ExactPersistedCacheHit demand) →
    CacheHitAdmission hit →
    CacheFirstResolution demand

  acquiredPersistedAndReused :
    (acquisition : GovernedAcquisitionReceipt demand) →
    exactDemandMatch acquisition ≡ true →
    PersistAfterAcquireReceipt acquisition →
    CacheFirstResolution demand

------------------------------------------------------------------------
-- Network accounting is structural, not advisory.
------------------------------------------------------------------------

networkRequestsForPGHit :
  ∀ {demand hit} →
  (admission : CacheHitAdmission {demand} hit) →
  Nat
networkRequestsForPGHit _ = zero

networkRequestsForAcquisition :
  ∀ {demand} →
  GovernedAcquisitionReceipt demand →
  Nat
networkRequestsForAcquisition = networkRequests

pgHitUsesZeroNetwork :
  ∀ {demand hit} →
  (admission : CacheHitAdmission {demand} hit) →
  networkRequestsForPGHit admission ≡ zero
pgHitUsesZeroNetwork _ = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PGHitMayCallNetwork : Set where
data PGMissMeansSourceAbsent : Set where
data PGMissMeansNegativeLegalEvidence : Set where
data MalformedCacheMeansSourceFalse : Set where
data DatabaseFailureMeansSourceAbsent : Set where
data PersistenceVerificationMayBeSkipped : Set where
data NearbyCachedSourceMayPayExactDemand : Set where
data CacheReceiptCreatesLegalAuthority : Set where

pgHitMayNotCallNetwork : PGHitMayCallNetwork → ⊥
pgHitMayNotCallNetwork ()

pgMissDoesNotMeanSourceAbsent : PGMissMeansSourceAbsent → ⊥
pgMissDoesNotMeanSourceAbsent ()

pgMissDoesNotMeanNegativeLegalEvidence : PGMissMeansNegativeLegalEvidence → ⊥
pgMissDoesNotMeanNegativeLegalEvidence ()

malformedCacheDoesNotMeanSourceFalse : MalformedCacheMeansSourceFalse → ⊥
malformedCacheDoesNotMeanSourceFalse ()

databaseFailureDoesNotMeanSourceAbsent : DatabaseFailureMeansSourceAbsent → ⊥
databaseFailureDoesNotMeanSourceAbsent ()

persistenceMustBeVerifiedByExactPGReuse : PersistenceVerificationMayBeSkipped → ⊥
persistenceMustBeVerifiedByExactPGReuse ()

nearbyCachedSourceDoesNotPayExactDemand : NearbyCachedSourceMayPayExactDemand → ⊥
nearbyCachedSourceDoesNotPayExactDemand ()

cacheReceiptDoesNotCreateLegalAuthority : CacheReceiptCreatesLegalAuthority → ⊥
cacheReceiptDoesNotCreateLegalAuthority ()

record OALCPostgresCacheFirstBoundary : Set where
  constructor oalc-postgres-cache-first-boundary
  field
    exactDemandMatchRequired : Bool
    pgCheckedBeforeNetwork : Bool
    pgHitNetworkRequestsZero : Bool
    missSchedulesGovernedAcquisition : Bool
    acquiredSourcePersisted : Bool
    postPersistPGReuseRequired : Bool
    missCreatesNegativeEvidence : Bool
    cacheCreatesLegalAuthority : Bool

canonicalOALCPostgresCacheFirstBoundary : OALCPostgresCacheFirstBoundary
canonicalOALCPostgresCacheFirstBoundary =
  oalc-postgres-cache-first-boundary
    true true true true true true false false
