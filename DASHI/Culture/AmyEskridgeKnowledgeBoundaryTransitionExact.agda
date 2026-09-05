module DASHI.Culture.AmyEskridgeKnowledgeBoundaryTransitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.KnowledgeBoundaryTransitionBidiExact as B

------------------------------------------------------------------------
-- ESKRIDGE 2020 RELEASE-REVIEW LEAD
--
-- The captured contemporaneous social-media artifact preserves a statement
-- attributed to Amy Eskridge.  It is a self-report about NASA-origin work,
-- private maturation and NASA public-release review.  No paper title, NASA case
-- number, approval notice or located final publication is supplied.
------------------------------------------------------------------------

amyNASAOriginPrivateWork : B.BoundaryStateReceipt
amyNASAOriginPrivateWork = B.boundary-state-receipt
  "Amy Eskridge / The Institute"
  "unnamed foundational work said to have originated with a team member while a NASA MSFC civil servant and later matured privately by The Institute"
  B.boundedPrivate
  B.capturedContemporaneousArtifact
  "Wayback capture of 2020 Alien_Scientist post preserving screenshot attributed to Amy Eskridge; later provenance review TR-0013"
  "The attributed statement says the foundational work originated at NASA MSFC, was subsequently matured privately, and required NASA public-release approval before related subsequent results could be discussed publicly. This is a self-report, not a NASA institutional restriction receipt."

amyPaperUnderReview : B.BoundaryStateReceipt
amyPaperUnderReview = B.boundary-state-receipt
  "Amy Eskridge / The Institute"
  "unnamed paper said to be based on the NASA-origin foundational work and subsequent private maturation"
  B.releaseUnderReview
  B.capturedContemporaneousArtifact
  "Wayback capture of 2020 Alien_Scientist post preserving screenshot attributed to Amy Eskridge; later provenance review TR-0013"
  "The attributed statement says a paper was under NASA review for publication and expected within roughly 30 days. No paper title, case number, NASA receipt, approval decision or final publication is supplied in the located artifact."

record AmyBoundaryTransitionFrontier : Set where
  constructor amy-boundary-transition-frontier
  field
    boundedStateSelfReported : Bool
    boundedStateSelfReportedIsTrue : boundedStateSelfReported ≡ true
    releaseReviewSelfReported : Bool
    releaseReviewSelfReportedIsTrue : releaseReviewSelfReported ≡ true
    primaryNASARestrictionReceiptLocated : Bool
    primaryNASARestrictionReceiptLocatedIsFalse :
      primaryNASARestrictionReceiptLocated ≡ false
    exactSameObjectWeldLocated : Bool
    exactSameObjectWeldLocatedIsFalse : exactSameObjectWeldLocated ≡ false
    releaseApprovalLocated : Bool
    releaseApprovalLocatedIsFalse : releaseApprovalLocated ≡ false
    finalPublicReleaseLocated : Bool
    finalPublicReleaseLocatedIsFalse : finalPublicReleaseLocated ≡ false
    completedBoundaryTransitionOwned : Bool
    completedBoundaryTransitionOwnedIsFalse :
      completedBoundaryTransitionOwned ≡ false

canonicalAmyBoundaryTransitionFrontier : AmyBoundaryTransitionFrontier
canonicalAmyBoundaryTransitionFrontier = amy-boundary-transition-frontier
  true refl
  true refl
  false refl
  false refl
  false refl
  false refl
  false refl

record AmyBoundaryAcquisitionTarget : Set where
  constructor amy-boundary-acquisition-target
  field
    requestedEvidence : String
    canPromote : String
    cannotPromote : String

amySameObjectTarget : AmyBoundaryAcquisitionTarget
amySameObjectTarget = amy-boundary-acquisition-target
  "paper title, NASA STI/IP case number, review receipt, draft/final version pair, correspondence, or other provenance that identifies the exact technical object across the private/review/public states"
  "an attempted or completed same-object boundary transition, depending on the recovered state sequence"
  "technical validity, suppression motive, targeting, actor identity, or cause of death"

amyOutcomeTarget : AmyBoundaryAcquisitionTarget
amyOutcomeTarget = amy-boundary-acquisition-target
  "NASA approval/denial/release record or located final publication tied to the same object"
  "the outcome of the 2020 release-review process"
  "a completed public transfer without a same-object weld"
