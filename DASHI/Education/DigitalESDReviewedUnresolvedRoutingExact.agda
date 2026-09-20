module DASHI.Education.DigitalESDReviewedUnresolvedRoutingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDTitleAbstractScreeningExact as Screen

------------------------------------------------------------------------
-- EXPLICITLY REVIEWED UNRESOLVED ROUTING
--
-- The authoritative four-way screening surface already distinguishes
-- include / probable / exclude / unresolved.  This owner refines unresolved
-- operationally without changing that authority:
--
--   pending unresolved
--       -> title/abstract review queue
--
--   explicitly reviewed unresolved
--       -> ambiguity receipt
--       -> optional full-text retrieval for screening resolution
--       -> still unresolved until a later explicit screening decision
--
-- Full-text obtained for screening resolution is not the same object as the
-- retained include/probable full-text lane used for downstream synthesis.
------------------------------------------------------------------------

data UnresolvedReviewState : Set where
  pendingTitleAbstractReview
  reviewedStillUnresolved
  : UnresolvedReviewState

data ResolutionReason : Set where
  insufficientTitleAbstractEvidence
  inaccessibleAbstract
  explicitRequiresFullText
  otherReviewedAmbiguity
  : ResolutionReason

record ReviewedUnresolvedReceipt : Set where
  constructor reviewed-unresolved-receipt
  field
    screeningDecisionReceipt : Screen.ScreeningDecisionReceipt
    sourceIdentityReference : String
    reviewReference : String
    reviewerOrProcessReference : String
    reason : ResolutionReason
    reviewedState : UnresolvedReviewState

    remainsUnresolved : Bool
    remainsUnresolvedIsTrue : remainsUnresolved ≡ true
    createsInclusion : Bool
    createsInclusionIsFalse : createsInclusion ≡ false
    createsExclusion : Bool
    createsExclusionIsFalse : createsExclusion ≡ false

open ReviewedUnresolvedReceipt public

record ScreeningResolutionFullTextRequest : Set where
  constructor screening-resolution-fulltext-request
  field
    reviewedUnresolved : ReviewedUnresolvedReceipt
    requestReference : String
    retrievalProcessReference : String

    purposeIsScreeningResolution : Bool
    purposeIsScreeningResolutionIsTrue :
      purposeIsScreeningResolution ≡ true

    createsScreeningInclusion : Bool
    createsScreeningInclusionIsFalse :
      createsScreeningInclusion ≡ false

    createsSourceTruth : Bool
    createsSourceTruthIsFalse :
      createsSourceTruth ≡ false

    createsSourceAuditAdmission : Bool
    createsSourceAuditAdmissionIsFalse :
      createsSourceAuditAdmission ≡ false

open ScreeningResolutionFullTextRequest public

data ReviewedUnresolvedCreatesInclusion : Set where
data ReviewedUnresolvedCreatesExclusion : Set where
data ScreeningResolutionFullTextCreatesSourceAuditAdmission : Set where
data ScreeningResolutionFullTextCreatesSourceTruth : Set where
data ReviewedUnresolvedMayReturnToTitleAbstractQueue : Set where
data ResolutionFullTextEqualsRetainedFullText : Set where

reviewedUnresolvedDoesNotCreateInclusion :
  ReviewedUnresolvedCreatesInclusion → ⊥
reviewedUnresolvedDoesNotCreateInclusion ()

reviewedUnresolvedDoesNotCreateExclusion :
  ReviewedUnresolvedCreatesExclusion → ⊥
reviewedUnresolvedDoesNotCreateExclusion ()

screeningResolutionFullTextDoesNotCreateSourceAuditAdmission :
  ScreeningResolutionFullTextCreatesSourceAuditAdmission → ⊥
screeningResolutionFullTextDoesNotCreateSourceAuditAdmission ()

screeningResolutionFullTextDoesNotCreateSourceTruth :
  ScreeningResolutionFullTextCreatesSourceTruth → ⊥
screeningResolutionFullTextDoesNotCreateSourceTruth ()

reviewedUnresolvedDoesNotReturnToTitleAbstractQueue :
  ReviewedUnresolvedMayReturnToTitleAbstractQueue → ⊥
reviewedUnresolvedDoesNotReturnToTitleAbstractQueue ()

resolutionFullTextIsNotRetainedFullText :
  ResolutionFullTextEqualsRetainedFullText → ⊥
resolutionFullTextIsNotRetainedFullText ()

record ReviewedUnresolvedRoutingBoundary : Set where
  constructor reviewed-unresolved-routing-boundary
  field
    pendingAndReviewedUnresolvedDistinct : Bool
    pendingAndReviewedUnresolvedDistinctIsTrue :
      pendingAndReviewedUnresolvedDistinct ≡ true

    reviewedUnresolvedLeavesTitleAbstractQueue : Bool
    reviewedUnresolvedLeavesTitleAbstractQueueIsTrue :
      reviewedUnresolvedLeavesTitleAbstractQueue ≡ true

    reviewedUnresolvedMaySeekFullTextForResolution : Bool
    reviewedUnresolvedMaySeekFullTextForResolutionIsTrue :
      reviewedUnresolvedMaySeekFullTextForResolution ≡ true

    fullTextResolutionCreatesInclusion : Bool
    fullTextResolutionCreatesInclusionIsFalse :
      fullTextResolutionCreatesInclusion ≡ false

    fullTextResolutionCreatesAuditAdmission : Bool
    fullTextResolutionCreatesAuditAdmissionIsFalse :
      fullTextResolutionCreatesAuditAdmission ≡ false

open ReviewedUnresolvedRoutingBoundary public

canonicalReviewedUnresolvedRoutingBoundary :
  ReviewedUnresolvedRoutingBoundary
canonicalReviewedUnresolvedRoutingBoundary =
  reviewed-unresolved-routing-boundary
    true refl
    true refl
    true refl
    false refl
    false refl
