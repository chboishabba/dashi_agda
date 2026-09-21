module DASHI.Education.DigitalESDSelectiveFullTextMaterialisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDTitleAbstractScreeningExact as Screen
import DASHI.Education.DigitalESDAdaptiveScreeningProgrammeExact as Adaptive

------------------------------------------------------------------------
-- SPARSE / BOUNDED FULL-TEXT MATERIALISATION
--
-- The exact ERIC metadata universe may be ~44k records.  That denominator is
-- not a command to fetch ~44k full-text artifacts.
--
-- Full-text bytes are a sparse cache over the authoritative include/probable
-- frontier.  The metadata corpus and screening ledger remain complete even
-- when only a bounded working set of full text is materialised.
------------------------------------------------------------------------

data CacheState : Set where
  metadataOnly : CacheState
  queuedForFetch : CacheState
  materialised : CacheState
  parsedOrReconciled : CacheState
  evictable : CacheState

record StorageBudget : Set where
  constructor storage-budget
  field
    maxMaterialisedItems : Nat
    maxCacheBytes : Nat
    reserveBytes : Nat
    batchItems : Nat
    policyReference : String

open StorageBudget public

record SparseFullTextCandidate : Set where
  constructor sparse-fulltext-candidate
  field
    screeningDecision : Screen.ScreeningDecisionReceipt
    retained :
      Adaptive.RetainedForFullText
        (Screen.decision screeningDecision)

    priorityReference : String
    cacheState : CacheState
    estimatedBytesReference : String
    alreadyCached : Bool
    alreadyCachedIsFalse : alreadyCached ≡ false
    fetchCreatesAdmission : Bool
    fetchCreatesAdmissionIsFalse : fetchCreatesAdmission ≡ false

open SparseFullTextCandidate public

record FullTextBatchPlan : Set where
  constructor fulltext-batch-plan
  field
    budget : StorageBudget
    selectedCount : Nat
    selectedEstimatedBytesReference : String
    planReference : String

    respectsItemCap : Bool
    respectsItemCapIsTrue : respectsItemCap ≡ true

    respectsByteCap : Bool
    respectsByteCapIsTrue : respectsByteCap ≡ true

    respectsReserve : Bool
    respectsReserveIsTrue : respectsReserve ≡ true

    onlyRetainedRecordsSelected : Bool
    onlyRetainedRecordsSelectedIsTrue :
      onlyRetainedRecordsSelected ≡ true

    metadataUniverseRemainsMetadataOnly : Bool
    metadataUniverseRemainsMetadataOnlyIsTrue :
      metadataUniverseRemainsMetadataOnly ≡ true

open FullTextBatchPlan public

record FullTextCacheReceipt : Set where
  constructor fulltext-cache-receipt
  field
    sourceIdentityReference : String
    sourceRevisionReference : String
    artifactReference : String
    artifactSha256 : String
    artifactBytes : Nat

    materialisedFromPlanReference : String
    parseOrInteropReceiptReference : String
    state : CacheState

    createsSourceTruth : Bool
    createsSourceTruthIsFalse : createsSourceTruth ≡ false

    createsSourceAuditAdmission : Bool
    createsSourceAuditAdmissionIsFalse :
      createsSourceAuditAdmission ≡ false

open FullTextCacheReceipt public

record EvictionEligibility : Set where
  constructor eviction-eligibility
  field
    cacheReceipt : FullTextCacheReceipt
    downstreamReceiptObserved : Bool
    downstreamReceiptObservedIsTrue :
      downstreamReceiptObserved ≡ true
    exactRevisionRetainedElsewhere : Bool
    exactRevisionRetainedElsewhereIsTrue :
      exactRevisionRetainedElsewhere ≡ true
    safeToEvictWorkingCopy : Bool
    safeToEvictWorkingCopyIsTrue :
      safeToEvictWorkingCopy ≡ true

open EvictionEligibility public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MetadataUniverseForcesFullTextMaterialisation : Set where
data UnreviewedRecordMayEnterFullTextBatch : Set where
data FullTextBatchMayIgnoreStorageBudget : Set where
data FullTextBatchMayIgnoreReserve : Set where
data CacheRegistrationCreatesSourceTruth : Set where
data CacheRegistrationCreatesSourceAuditAdmission : Set where
data UnprocessedArtifactMayBeEvictedAsPaid : Set where
data EvictionMayEraseRevisionIdentity : Set where
data FullTextAvailabilityMetadataCreatesFetchObligation : Set where

metadataUniverseDoesNotForceFullTextMaterialisation :
  MetadataUniverseForcesFullTextMaterialisation → ⊥
metadataUniverseDoesNotForceFullTextMaterialisation ()

unreviewedRecordDoesNotEnterFullTextBatch :
  UnreviewedRecordMayEnterFullTextBatch → ⊥
unreviewedRecordDoesNotEnterFullTextBatch ()

fullTextBatchDoesNotIgnoreStorageBudget :
  FullTextBatchMayIgnoreStorageBudget → ⊥
fullTextBatchDoesNotIgnoreStorageBudget ()

fullTextBatchDoesNotIgnoreReserve :
  FullTextBatchMayIgnoreReserve → ⊥
fullTextBatchDoesNotIgnoreReserve ()

cacheRegistrationDoesNotCreateSourceTruth :
  CacheRegistrationCreatesSourceTruth → ⊥
cacheRegistrationDoesNotCreateSourceTruth ()

cacheRegistrationDoesNotCreateSourceAuditAdmission :
  CacheRegistrationCreatesSourceAuditAdmission → ⊥
cacheRegistrationDoesNotCreateSourceAuditAdmission ()

unprocessedArtifactDoesNotBecomeEvictable :
  UnprocessedArtifactMayBeEvictedAsPaid → ⊥
unprocessedArtifactDoesNotBecomeEvictable ()

evictionDoesNotEraseRevisionIdentity :
  EvictionMayEraseRevisionIdentity → ⊥
evictionDoesNotEraseRevisionIdentity ()

fullTextAvailabilityMetadataDoesNotCreateFetchObligation :
  FullTextAvailabilityMetadataCreatesFetchObligation → ⊥
fullTextAvailabilityMetadataDoesNotCreateFetchObligation ()

record SparseMaterialisationBoundary : Set where
  constructor sparse-materialisation-boundary
  field
    metadataCorpusMayExceedMaterialisedCorpus : Bool
    metadataCorpusMayExceedMaterialisedCorpusIsTrue :
      metadataCorpusMayExceedMaterialisedCorpus ≡ true

    onlyIncludeProbableCanEscalate : Bool
    onlyIncludeProbableCanEscalateIsTrue :
      onlyIncludeProbableCanEscalate ≡ true

    defaultIsMetadataOnly : Bool
    defaultIsMetadataOnlyIsTrue :
      defaultIsMetadataOnly ≡ true

    boundedBatchRequired : Bool
    boundedBatchRequiredIsTrue :
      boundedBatchRequired ≡ true

    storageReserveRequired : Bool
    storageReserveRequiredIsTrue :
      storageReserveRequired ≡ true

    downstreamReceiptRequiredBeforeEviction : Bool
    downstreamReceiptRequiredBeforeEvictionIsTrue :
      downstreamReceiptRequiredBeforeEviction ≡ true

    cacheStateCreatesAdmission : Bool
    cacheStateCreatesAdmissionIsFalse :
      cacheStateCreatesAdmission ≡ false

open SparseMaterialisationBoundary public

canonicalSparseMaterialisationBoundary : SparseMaterialisationBoundary
canonicalSparseMaterialisationBoundary =
  sparse-materialisation-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl

sparseMaterialisationReading : String
sparseMaterialisationReading =
  "Digital-ESD retains the full bibliographic/screening denominator while materialising only a bounded sparse full-text working set. The default state for the corpus is metadata-only. Only authoritative include/probable screening receipts may enter a fetch batch. Each batch must respect item and byte caps plus a storage reserve. Cache registration, parsing and eviction create neither source truth nor SourceAuditAdmission. A working copy is evictable only after a downstream parse/interop receipt exists and exact revision identity remains retained elsewhere."
