module DASHI.Cognition.PNF.SensibLawReviewProjectionEconomyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

import DASHI.Cognition.PNF.RuntimeThroughputConstitution as Throughput

------------------------------------------------------------------------
-- SCALE-1.P review-projection economy.
--
-- Review candidates/decisions are semantic/workflow objects.  The materialized
-- workstation projection is a physical consumer product over those objects.
-- Reopening an unchanged projection is therefore distinct from making a review
-- decision, paying semantic admission, or promoting claim truth.
------------------------------------------------------------------------

record ReviewProjectionInputIdentity : Set where
  constructor review-projection-input-identity
  field
    sourceRevisionRef : String
    algorithmRef : String
    inputFingerprintRef : String
    consumerScopeRef : String

open ReviewProjectionInputIdentity public

record ExactReviewProjectionReuse : Set where
  constructor exact-review-projection-reuse
  field
    inputIdentity : ReviewProjectionInputIdentity
    reviewItemRefs : List String

    exactInputIdentityMatched : Bool
    exactInputIdentityMatchedIsTrue :
      exactInputIdentityMatched ≡ true

    persistedProjectionComplete : Bool
    persistedProjectionCompleteIsTrue :
      persistedProjectionComplete ≡ true

    persistedItemsReopened : Bool
    persistedItemsReopenedIsTrue :
      persistedItemsReopened ≡ true

    recomputesReviewCandidates : Bool
    recomputesReviewCandidatesIsFalse :
      recomputesReviewCandidates ≡ false

    createsReviewDecision : Bool
    createsReviewDecisionIsFalse :
      createsReviewDecision ≡ false

    createsSemanticAdmission : Bool
    createsSemanticAdmissionIsFalse :
      createsSemanticAdmission ≡ false

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

    createsEventAssembly : Bool
    createsEventAssemblyIsFalse :
      createsEventAssembly ≡ false

    createsClaimTruth : Bool
    createsClaimTruthIsFalse :
      createsClaimTruth ≡ false

open ExactReviewProjectionReuse public

------------------------------------------------------------------------
-- Physical work accounting for the review consumer projection.
------------------------------------------------------------------------

record ReviewProjectionWorkReceipt : Set where
  constructor review-projection-work-receipt
  field
    workloadId : String

    inputCandidateRows : Nat
    inputPressureRows : Nat

    scannedRows : Nat
    admittedRows : Nat
    groupedRows : Nat
    outputItems : Nat
    attemptedWrites : Nat
    commitCount : Nat

    existingProductHits : Nat
    productsCreated : Nat
    rowsInserted : Nat
    rowsUpdated : Nat
    rowsUnchanged : Nat

    loadElapsedUnits : Nat
    joinFilterElapsedUnits : Nat
    groupElapsedUnits : Nat
    writeElapsedUnits : Nat
    reopenElapsedUnits : Nat

open ReviewProjectionWorkReceipt public

------------------------------------------------------------------------
-- Same-workload parser-relative certification remains owned by the existing
-- throughput constitution.  Review measurements may contribute the post-parser
-- stage, but may not manufacture a parser measurement from an exact replay in
-- which parser work was reused.
------------------------------------------------------------------------

record ReviewProjectionParserRelativeEvidence : Set where
  constructor review-projection-parser-relative-evidence
  field
    parserStage : Throughput.StageCostReceipt
    reviewStage : Throughput.StageCostReceipt

    sameWorkload :
      Throughput.workloadId parserStage
      ≡ Throughput.workloadId reviewStage

open ReviewProjectionParserRelativeEvidence public

data ReusedParserWallIsFreshParserMeasurement : Set where
data ReviewProjectionReuseCreatesReviewDecision : Set where
data ReviewProjectionReuseCreatesSemanticAdmission : Set where
data ReviewProjectionReuseCreatesSemanticAuthority : Set where
data ReviewProjectionReuseCreatesEventAssembly : Set where
data ReviewProjectionReuseCreatesClaimTruth : Set where
data ReviewProjectionCacheKeyMayIgnoreInputFingerprint : Set where
data ReviewProjectionCacheKeyMayIgnoreConsumerScope : Set where
data ReviewProjectionCacheKeyMayIgnoreOccurrenceAncestry : Set where
data ReviewProjectionElapsedAloneProvesParserDominance : Set where

reusedParserWallDoesNotBecomeFreshParserMeasurement :
  ReusedParserWallIsFreshParserMeasurement → ⊥
reusedParserWallDoesNotBecomeFreshParserMeasurement ()

reviewProjectionReuseDoesNotCreateReviewDecision :
  ReviewProjectionReuseCreatesReviewDecision → ⊥
reviewProjectionReuseDoesNotCreateReviewDecision ()

reviewProjectionReuseDoesNotCreateSemanticAdmission :
  ReviewProjectionReuseCreatesSemanticAdmission → ⊥
reviewProjectionReuseDoesNotCreateSemanticAdmission ()

reviewProjectionReuseDoesNotCreateSemanticAuthority :
  ReviewProjectionReuseCreatesSemanticAuthority → ⊥
reviewProjectionReuseDoesNotCreateSemanticAuthority ()

reviewProjectionReuseDoesNotCreateEventAssembly :
  ReviewProjectionReuseCreatesEventAssembly → ⊥
reviewProjectionReuseDoesNotCreateEventAssembly ()

reviewProjectionReuseDoesNotCreateClaimTruth :
  ReviewProjectionReuseCreatesClaimTruth → ⊥
reviewProjectionReuseDoesNotCreateClaimTruth ()

reviewProjectionCacheMustTrackInputFingerprint :
  ReviewProjectionCacheKeyMayIgnoreInputFingerprint → ⊥
reviewProjectionCacheMustTrackInputFingerprint ()

reviewProjectionCacheMustTrackConsumerScope :
  ReviewProjectionCacheKeyMayIgnoreConsumerScope → ⊥
reviewProjectionCacheMustTrackConsumerScope ()

reviewProjectionCacheMustTrackOccurrenceAncestry :
  ReviewProjectionCacheKeyMayIgnoreOccurrenceAncestry → ⊥
reviewProjectionCacheMustTrackOccurrenceAncestry ()

reviewProjectionWallAloneCannotProveParserDominance :
  ReviewProjectionElapsedAloneProvesParserDominance → ⊥
reviewProjectionWallAloneCannotProveParserDominance ()

------------------------------------------------------------------------
-- Canonical semantic/physical boundary.
------------------------------------------------------------------------

record ReviewProjectionEconomyBoundary : Set where
  constructor review-projection-economy-boundary
  field
    reviewProjectionIsConsumerMaterialization : Bool
    reviewProjectionIsConsumerMaterializationIsTrue :
      reviewProjectionIsConsumerMaterialization ≡ true

    exactProjectionMayBeReused : Bool
    exactProjectionMayBeReusedIsTrue :
      exactProjectionMayBeReused ≡ true

    inputFingerprintIsPartOfReuseIdentity : Bool
    inputFingerprintIsPartOfReuseIdentityIsTrue :
      inputFingerprintIsPartOfReuseIdentity ≡ true

    consumerScopeIsPartOfReuseIdentity : Bool
    consumerScopeIsPartOfReuseIdentityIsTrue :
      consumerScopeIsPartOfReuseIdentity ≡ true

    occurrenceAncestryIsPartOfReuseIdentity : Bool
    occurrenceAncestryIsPartOfReuseIdentityIsTrue :
      occurrenceAncestryIsPartOfReuseIdentity ≡ true

    projectionReusePaysReviewDecision : Bool
    projectionReusePaysReviewDecisionIsFalse :
      projectionReusePaysReviewDecision ≡ false

    projectionReusePaysSemanticAdmission : Bool
    projectionReusePaysSemanticAdmissionIsFalse :
      projectionReusePaysSemanticAdmission ≡ false

    projectionReuseCreatesClaimTruth : Bool
    projectionReuseCreatesClaimTruthIsFalse :
      projectionReuseCreatesClaimTruth ≡ false

    parserDominanceRequiresSameWorkloadMeasurement : Bool
    parserDominanceRequiresSameWorkloadMeasurementIsTrue :
      parserDominanceRequiresSameWorkloadMeasurement ≡ true

open ReviewProjectionEconomyBoundary public

canonicalReviewProjectionEconomyBoundary : ReviewProjectionEconomyBoundary
canonicalReviewProjectionEconomyBoundary =
  review-projection-economy-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl


------------------------------------------------------------------------
-- SCALE-1.P v2: the review cache may replace a direct occurrence hash with
-- the exact identity of a completed upstream reconciliation product.
--
-- Occurrence ancestry is not forgotten: it is paid by the upstream L2 stage
-- receipt.  Review projection therefore need not rescan the same occurrence
-- rows merely to rediscover that the upstream product is unchanged.
------------------------------------------------------------------------

record ReviewProjectionUpstreamIdentity : Set where
  constructor review-projection-upstream-identity
  field
    sourceRevisionRefV2 : String
    parserRunRefV2 : String
    reconciliationDetectorRefV2 : String
    reviewAlgorithmRefV2 : String
    consumerScopeRefV2 : String

    upstreamReconciliationComplete : Bool
    upstreamReconciliationCompleteIsTrue :
      upstreamReconciliationComplete ≡ true

    upstreamCandidateOnly : Bool
    upstreamCandidateOnlyIsTrue :
      upstreamCandidateOnly ≡ true

    upstreamCreatesSemanticAuthority : Bool
    upstreamCreatesSemanticAuthorityIsFalse :
      upstreamCreatesSemanticAuthority ≡ false

    upstreamCreatesEntityIdentity : Bool
    upstreamCreatesEntityIdentityIsFalse :
      upstreamCreatesEntityIdentity ≡ false

    upstreamCreatesPropositionIdentity : Bool
    upstreamCreatesPropositionIdentityIsFalse :
      upstreamCreatesPropositionIdentity ≡ false

    upstreamCreatesEventIdentity : Bool
    upstreamCreatesEventIdentityIsFalse :
      upstreamCreatesEventIdentity ≡ false

    upstreamCreatesClaimTruth : Bool
    upstreamCreatesClaimTruthIsFalse :
      upstreamCreatesClaimTruth ≡ false

open ReviewProjectionUpstreamIdentity public

record ExactReviewProjectionReuseV2 : Set where
  constructor exact-review-projection-reuse-v2
  field
    upstreamIdentity : ReviewProjectionUpstreamIdentity
    reviewItemRefsV2 : List String

    persistedProjectionCompleteV2 : Bool
    persistedProjectionCompleteV2IsTrue :
      persistedProjectionCompleteV2 ≡ true

    persistedItemsReopenedV2 : Bool
    persistedItemsReopenedV2IsTrue :
      persistedItemsReopenedV2 ≡ true

    pressureRowsScannedOnReuse : Nat
    pressureRowsScannedOnReuseZero :
      pressureRowsScannedOnReuse ≡ 0

    contestationRowsScannedOnReuse : Nat
    contestationRowsScannedOnReuseZero :
      contestationRowsScannedOnReuse ≡ 0

    occurrenceRowsScannedOnReuse : Nat
    occurrenceRowsScannedOnReuseZero :
      occurrenceRowsScannedOnReuse ≡ 0

    occurrenceLookupCountOnReuse : Nat
    occurrenceLookupCountOnReuseZero :
      occurrenceLookupCountOnReuse ≡ 0

    createsReviewDecisionV2 : Bool
    createsReviewDecisionV2IsFalse :
      createsReviewDecisionV2 ≡ false

    createsSemanticAdmissionV2 : Bool
    createsSemanticAdmissionV2IsFalse :
      createsSemanticAdmissionV2 ≡ false

    createsSemanticAuthorityV2 : Bool
    createsSemanticAuthorityV2IsFalse :
      createsSemanticAuthorityV2 ≡ false

    createsClaimTruthV2 : Bool
    createsClaimTruthV2IsFalse :
      createsClaimTruthV2 ≡ false

open ExactReviewProjectionReuseV2 public

data ReviewProjectionV2CacheMayIgnoreParserRun : Set where
data ReviewProjectionV2CacheMayIgnoreReconciliationDetector : Set where
data ReviewProjectionV2CacheMayIgnoreUpstreamCompletion : Set where
data ReviewProjectionV2CacheMayIgnoreConsumerScope : Set where
data ReviewProjectionV2ReuseMayRescanOccurrences : Set where

reviewProjectionV2CacheMustTrackParserRun :
  ReviewProjectionV2CacheMayIgnoreParserRun → ⊥
reviewProjectionV2CacheMustTrackParserRun ()

reviewProjectionV2CacheMustTrackReconciliationDetector :
  ReviewProjectionV2CacheMayIgnoreReconciliationDetector → ⊥
reviewProjectionV2CacheMustTrackReconciliationDetector ()

reviewProjectionV2CacheRequiresCompletedUpstreamProduct :
  ReviewProjectionV2CacheMayIgnoreUpstreamCompletion → ⊥
reviewProjectionV2CacheRequiresCompletedUpstreamProduct ()

reviewProjectionV2CacheMustTrackConsumerScope :
  ReviewProjectionV2CacheMayIgnoreConsumerScope → ⊥
reviewProjectionV2CacheMustTrackConsumerScope ()

reviewProjectionV2ExactReuseDoesNotRescanOccurrences :
  ReviewProjectionV2ReuseMayRescanOccurrences → ⊥
reviewProjectionV2ExactReuseDoesNotRescanOccurrences ()
