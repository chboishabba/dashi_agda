module DASHI.Core.KnowledgeBoundaryTransitionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- KNOWLEDGE-BOUNDARY TRANSITION BIDI
--
-- A completed restricted/private -> public transfer is not the only observable
-- state.  Attempts, review, approval, rejection and unresolved outcomes are
-- retained separately so an attempted release is not promoted to publication.
------------------------------------------------------------------------

data BoundaryState : Set where
  boundedPrivate
  releaseRequested
  releaseUnderReview
  releaseApproved
  releasedPublicly
  releaseDenied
  releaseOutcomeUnresolved
  : BoundaryState

data BoundaryEvidenceGrade : Set where
  primaryInstitutional
  firstPersonContemporaneous
  capturedContemporaneousArtifact
  laterSecondary
  uncorroboratedAttribution
  : BoundaryEvidenceGrade

record BoundaryStateReceipt : Set where
  constructor boundary-state-receipt
  field
    personOrTeam : String
    knowledgeObject : String
    state : BoundaryState
    evidenceGrade : BoundaryEvidenceGrade
    sourceReference : String
    boundedReading : String

open BoundaryStateReceipt public

record SameBoundaryObject
    (left right : BoundaryStateReceipt) : Set where
  constructor same-boundary-object
  field
    objectIdentityReference : String
    sameObjectClaim : String

open SameBoundaryObject public

record AttemptedBoundaryTransition
    (bounded request : BoundaryStateReceipt) : Set where
  constructor attempted-boundary-transition
  field
    boundedState : state bounded ≡ boundedPrivate
    requestedState :
      (state request ≡ releaseRequested) ⊎
      (state request ≡ releaseUnderReview)
    sameObject : SameBoundaryObject bounded request
    transitionReference : String

open AttemptedBoundaryTransition public

record CompletedBoundaryTransition
    (bounded public : BoundaryStateReceipt) : Set where
  constructor completed-boundary-transition
  field
    boundedState : state bounded ≡ boundedPrivate
    publicState : state public ≡ releasedPublicly
    sameObject : SameBoundaryObject bounded public
    transitionReference : String

open CompletedBoundaryTransition public

record BoundaryTransitionBoundary : Set where
  constructor boundary-transition-boundary
  field
    releaseRequestedMeansReleased : Bool
    releaseRequestedMeansReleasedIsFalse : releaseRequestedMeansReleased ≡ false
    underReviewMeansApproved : Bool
    underReviewMeansApprovedIsFalse : underReviewMeansApproved ≡ false
    approvalMeansPublicRelease : Bool
    approvalMeansPublicReleaseIsFalse : approvalMeansPublicRelease ≡ false
    attemptedTransitionMeansCompletedTransition : Bool
    attemptedTransitionMeansCompletedTransitionIsFalse :
      attemptedTransitionMeansCompletedTransition ≡ false
    selfReportOfReviewEqualsInstitutionalReviewReceipt : Bool
    selfReportOfReviewEqualsInstitutionalReviewReceiptIsFalse :
      selfReportOfReviewEqualsInstitutionalReviewReceipt ≡ false

canonicalBoundaryTransitionBoundary : BoundaryTransitionBoundary
canonicalBoundaryTransitionBoundary = boundary-transition-boundary
  false refl
  false refl
  false refl
  false refl
  false refl
