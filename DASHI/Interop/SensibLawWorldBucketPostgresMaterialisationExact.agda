module DASHI.Interop.SensibLawWorldBucketPostgresMaterialisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- SENSIBLAW WORLD-BUCKET POSTGRES MATERIALISATION PARITY
--
-- Runtime owners:
--   chboishabba/SensibLaw :: src/ontology/wikimedia_world_walk.py
--   chboishabba/SensibLaw :: src/storage/postgres/world_bucket_store.py
-- Migration:
--   database/postgres_migrations/182_world_bucket_append_only_materialisation.sql
--
-- Postgres is a durable materialisation layer for a bounded local inquiry
-- bucket.  It is not semantic authority and it is not the eRDFa/IPFS
-- publication boundary.
------------------------------------------------------------------------

data MaterialisationState : Set where
  skeleton referenceOnly fullLocal coldLocal federatedOnly : MaterialisationState

data WorldBucketTableFamily : Set where
  bucketTable
  bucketNodeTable
  growthReceiptTable
  projectionTable
  projectionMemberTable
  projectionParentTable
  materialisationReceiptTable : WorldBucketTableFamily

worldBucketTableFamilyCount : Nat
worldBucketTableFamilyCount = 7

record PostgresWorldBucketBoundary : Set where
  constructor postgresWorldBucketBoundary
  field
    normalizedTables : Bool
    jsonPayloadRequired : Bool
    jsonbPayloadRequired : Bool
    growthReceiptsTyped : Bool
    projectionMembersExplicit : Bool
    projectionParentsExplicit : Bool
    materialisationReceiptsAppendOnly : Bool
    replayUsesInsertDoNothing : Bool
    updateMayRewritePriorEvidence : Bool
    deleteMayErasePriorEvidence : Bool
    projectionCandidateOnly : Bool
    projectionPerformsSemanticPromotion : Bool
    projectionIsBrowsingHistory : Bool
    liveIPFSPublicationPerformed : Bool
    localMaterialisationCreatesAuthority : Bool

open PostgresWorldBucketBoundary public

canonicalPostgresWorldBucketBoundary : PostgresWorldBucketBoundary
canonicalPostgresWorldBucketBoundary =
  postgresWorldBucketBoundary
    true
    false
    false
    true
    true
    true
    true
    true
    false
    false
    true
    false
    false
    false
    false

record ConsumerAdequacyBoundary : Set where
  constructor consumerAdequacyBoundary
  field
    navigationMayUseSkeleton : Bool
    graphFollowMayUseReferenceOnly : Bool
    exactQuotationMayUseSkeletonWithoutBytes : Bool
    strictPrimaryAuthorityReviewMayUseSkeletonWithoutBytes : Bool
    exactSourceCanRequireFullMaterialisation : Bool
    fullMaterialisationAutomaticallyPaysEvidence : Bool

open ConsumerAdequacyBoundary public

canonicalConsumerAdequacyBoundary : ConsumerAdequacyBoundary
canonicalConsumerAdequacyBoundary =
  consumerAdequacyBoundary true true false false true false

record MaterialisationAuthorityBoundary : Set where
  constructor materialisationAuthorityBoundary
  field
    skeletonPreservesObjectIdentityCoordinate : Bool
    referenceOnlyMayPreserveLocator : Bool
    fullLocalMayPreserveVerifiedDigest : Bool
    coldLocalStillCountsAsPossession : Bool
    federatedOnlyMayBeReacquired : Bool
    possessionEqualsAuthority : Bool
    locatorAvailabilityEqualsTruth : Bool

open MaterialisationAuthorityBoundary public

canonicalMaterialisationAuthorityBoundary : MaterialisationAuthorityBoundary
canonicalMaterialisationAuthorityBoundary =
  materialisationAuthorityBoundary true true true true true false false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PostgresPersistenceCreatesSemanticAuthority : Set where
data LocalPossessionCreatesAuthority : Set where
data SkeletonPaysExactQuotation : Set where
data SkeletonPaysStrictPrimaryAuthorityReview : Set where
data ProjectionPublishesBrowsingHistory : Set where
data ReplayRewritesPriorEvidence : Set where
data MaterialisationReceiptPromotesTruth : Set where
data LocatorAvailabilityPaysEvidence : Set where

postgresPersistenceIsNotSemanticAuthority : PostgresPersistenceCreatesSemanticAuthority → ⊥
postgresPersistenceIsNotSemanticAuthority ()

localPossessionIsNotAuthority : LocalPossessionCreatesAuthority → ⊥
localPossessionIsNotAuthority ()

skeletonCannotPayExactQuotation : SkeletonPaysExactQuotation → ⊥
skeletonCannotPayExactQuotation ()

skeletonCannotPayStrictPrimaryAuthorityReview : SkeletonPaysStrictPrimaryAuthorityReview → ⊥
skeletonCannotPayStrictPrimaryAuthorityReview ()

publicationProjectionIsNotBrowsingHistory : ProjectionPublishesBrowsingHistory → ⊥
publicationProjectionIsNotBrowsingHistory ()

replayCannotRewritePriorEvidence : ReplayRewritesPriorEvidence → ⊥
replayCannotRewritePriorEvidence ()

materialisationReceiptDoesNotPromoteTruth : MaterialisationReceiptPromotesTruth → ⊥
materialisationReceiptDoesNotPromoteTruth ()

locatorAvailabilityDoesNotPayEvidence : LocatorAvailabilityPaysEvidence → ⊥
locatorAvailabilityDoesNotPayEvidence ()
