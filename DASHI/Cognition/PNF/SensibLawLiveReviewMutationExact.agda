module DASHI.Cognition.PNF.SensibLawLiveReviewMutationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawReviewWorkstationExact as Review

------------------------------------------------------------------------
-- S29.2 live persisted review mutation.
--
-- The runtime implementation locks the persisted ReviewItem, applies the
-- existing typed reducer, persists the ReviewReceipt and status transition in
-- the same transaction, then returns the resulting item to the operator UI.
--
-- This owner pins the semantic boundary of that implementation. Persistence
-- makes review state durable; it does not turn review state into truth.
------------------------------------------------------------------------

record PersistedReviewCommandBoundary : Set where
  constructor persisted-review-command-boundary
  field
    commandRef : String
    reviewItemRef : String
    reviewerRef : String
    action : Review.ReviewAction
    typedReducerUsed : Bool
    typedReducerUsedIsTrue : typedReducerUsed ≡ true
    itemLockedBeforeReduction : Bool
    itemLockedBeforeReductionIsTrue : itemLockedBeforeReduction ≡ true
    receiptAndStatusTransactional : Bool
    receiptAndStatusTransactionalIsTrue : receiptAndStatusTransactional ≡ true
    resultingItemReloaded : Bool
    resultingItemReloadedIsTrue : resultingItemReloaded ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open PersistedReviewCommandBoundary public

canonicalPersistedReviewCommandBoundary :
  PersistedReviewCommandBoundary
canonicalPersistedReviewCommandBoundary =
  persisted-review-command-boundary
    "review-command"
    "review-item"
    "reviewer"
    Review.accept
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- The live UI exposes the same typed actions as S29.
------------------------------------------------------------------------

record LiveReviewActionSurface : Set where
  constructor live-review-action-surface
  field
    acceptLive : Bool
    rejectLive : Bool
    abstainLive : Bool
    qualifyLive : Bool
    supersedeLive : Bool
    requestEvidenceLive : Bool
    openSourceLive : Bool
    followAuthorityLive : Bool
    qualificationRequiresExplicitRef : Bool
    evidenceRequestRequiresExplicitRef : Bool
    navigationPreservesReviewStatus : Bool

canonicalLiveReviewActionSurface : LiveReviewActionSurface
canonicalLiveReviewActionSurface =
  live-review-action-surface
    true true true true true true true true
    true true true

liveOpenSourcePreservesStatus :
  ∀ {status} →
  Review.nextStatus status Review.openSource ≡ status
liveOpenSourcePreservesStatus = Review.openSourcePreservesReviewStatus

liveFollowAuthorityPreservesStatus :
  ∀ {status} →
  Review.nextStatus status Review.followAuthority ≡ status
liveFollowAuthorityPreservesStatus =
  Review.followAuthorityPreservesReviewStatus

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DurableReviewStateCreatesTruth : Set where
data DatabaseCommitCreatesSemanticAuthority : Set where
data AcceptedStatusPaysApplicability : Set where
data SourceOpenRequestMeansEvidenceReviewed : Set where
data FollowAuthorityRequestMeansAuthorityResolved : Set where
data QualificationMayInventMissingRef : Set where
data EvidenceRequestMayInventMissingRef : Set where

durableReviewStateDoesNotCreateTruth :
  DurableReviewStateCreatesTruth → ⊥
durableReviewStateDoesNotCreateTruth ()

databaseCommitDoesNotCreateSemanticAuthority :
  DatabaseCommitCreatesSemanticAuthority → ⊥
databaseCommitDoesNotCreateSemanticAuthority ()

acceptedStatusDoesNotPayApplicability :
  AcceptedStatusPaysApplicability → ⊥
acceptedStatusDoesNotPayApplicability ()

sourceOpenRequestDoesNotMeanEvidenceReviewed :
  SourceOpenRequestMeansEvidenceReviewed → ⊥
sourceOpenRequestDoesNotMeanEvidenceReviewed ()

followAuthorityRequestDoesNotResolveAuthority :
  FollowAuthorityRequestMeansAuthorityResolved → ⊥
followAuthorityRequestDoesNotResolveAuthority ()

qualificationCannotInventMissingRef :
  QualificationMayInventMissingRef → ⊥
qualificationCannotInventMissingRef ()

evidenceRequestCannotInventMissingRef :
  EvidenceRequestMayInventMissingRef → ⊥
evidenceRequestCannotInventMissingRef ()
