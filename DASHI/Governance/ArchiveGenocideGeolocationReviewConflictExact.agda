module DASHI.Governance.ArchiveGenocideGeolocationReviewConflictExact where

open import DASHI.Core.Prelude

import DASHI.Governance.ArchiveGenocideGeolocationAntiTargetingExact as Geo

------------------------------------------------------------------------
-- REVIEW / CONFLICT PUBLICATION SEMANTICS
--
-- A reviewed consensus claim and a reviewed conflict are both publishable
-- epistemic states.  Awaiting-review and user-suggestion-under-review states
-- are not promoted merely because a disclosure consumer exists.
------------------------------------------------------------------------

data ReviewPublishable : Geo.GeolocationReviewState → Set where
  reviewedPublishable : ReviewPublishable Geo.reviewed
  conflictingSourcesPublishable : ReviewPublishable Geo.conflictingSources

awaitingReviewIsNotPublishable :
  ReviewPublishable Geo.awaitingReview → ⊥
awaitingReviewIsNotPublishable ()

suggestionUnderReviewIsNotPublishable :
  ReviewPublishable Geo.suggestionUnderReview → ⊥
suggestionUnderReviewIsNotPublishable ()

record PublishableDisclosureReceipt
    (evidence : Geo.GeolocationEvidence)
    (consumer : Geo.GeolocationConsumer)
    (disclosedPrecision : Geo.LocationPrecision) : Set where
  constructor publishable-disclosure-receipt
  field
    evidenceConsumer : Geo.EvidenceConsumer consumer
    reviewPublishable : ReviewPublishable (Geo.reviewState evidence)
    safeTemporal : Geo.SafeTemporal (Geo.temporalClass evidence)
    protectedPrecisionSafe :
      Geo.ProtectedPrecisionSafe
        (Geo.subjectProtection evidence)
        disclosedPrecision
    provenanceRetained : Bool
    provenanceRetainedIsTrue : provenanceRetained ≡ true
    reviewStateRetained : Bool
    reviewStateRetainedIsTrue : reviewStateRetained ≡ true
    thirdPartyOriginRetained : Bool
    thirdPartyOriginRetainedIsTrue : thirdPartyOriginRetained ≡ true

open PublishableDisclosureReceipt public

operationalTargetingPublishableReleaseImpossible :
  ∀ {evidence precision} →
  PublishableDisclosureReceipt
    evidence Geo.operationalTargetingConsumer precision → ⊥
operationalTargetingPublishableReleaseImpossible receipt =
  Geo.operationalTargetingConsumerIsNotEvidenceConsumer
    (evidenceConsumer receipt)

nearRealTimePublishableReleaseImpossible :
  ∀ {evidence consumer precision} →
  Geo.temporalClass evidence ≡ Geo.nearRealTime →
  PublishableDisclosureReceipt evidence consumer precision → ⊥
nearRealTimePublishableReleaseImpossible refl receipt =
  Geo.nearRealTimeIsNotSafeTemporal (safeTemporal receipt)

protectedExactPublishableReleaseImpossible :
  ∀ {evidence consumer} →
  Geo.subjectProtection evidence ≡ Geo.protectedPerson →
  PublishableDisclosureReceipt evidence consumer Geo.exactCoordinate → ⊥
protectedExactPublishableReleaseImpossible refl receipt =
  Geo.protectedExactPrecisionIsNotSafe (protectedPrecisionSafe receipt)

------------------------------------------------------------------------
-- Literal conflict-state witness: conflict is retained, not collapsed into a
-- consensus proof and not rejected merely for being conflict.
------------------------------------------------------------------------

conflictStateIsPublishable : ReviewPublishable Geo.conflictingSources
conflictStateIsPublishable = conflictingSourcesPublishable

data ConflictCollapsedIntoReviewed : Set where

conflictCannotBeSilentlyPromotedToReviewed :
  ConflictCollapsedIntoReviewed → ⊥
conflictCannotBeSilentlyPromotedToReviewed ()

record ReviewConflictBoundary : Set where
  constructor review-conflict-boundary
  field
    reviewedConsensusPublishable : Bool
    reviewedConsensusPublishableIsTrue :
      reviewedConsensusPublishable ≡ true

    reviewedConflictPublishable : Bool
    reviewedConflictPublishableIsTrue : reviewedConflictPublishable ≡ true

    awaitingReviewPublishable : Bool
    awaitingReviewPublishableIsFalse : awaitingReviewPublishable ≡ false

    suggestionUnderReviewPublishable : Bool
    suggestionUnderReviewPublishableIsFalse :
      suggestionUnderReviewPublishable ≡ false

    publishableConflictMeansConsensus : Bool
    publishableConflictMeansConsensusIsFalse :
      publishableConflictMeansConsensus ≡ false

    conflictStateMustSurvivePublication : Bool
    conflictStateMustSurvivePublicationIsTrue :
      conflictStateMustSurvivePublication ≡ true

open ReviewConflictBoundary public

canonicalReviewConflictBoundary : ReviewConflictBoundary
canonicalReviewConflictBoundary =
  review-conflict-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
