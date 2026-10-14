module DASHI.Cognition.OracleEllisonExactReviewPromotionGateExact where

------------------------------------------------------------------------
-- EXACT HUMAN-REVIEW PROMOTION GATE
--
-- Source acquisition, formal extraction and human review are independent
-- coordinates.  This owner reuses the master-owned generic REAL-MATTER review
-- receipt/binding without importing the legal evidence-role semantics.
--
-- Review can qualify an exact source/claim extraction for downstream use.  It
-- does not manufacture source authority, historical truth, causal
-- identification, institutional authority or a higher promotion level.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Law.SensibLawRealMatterReviewDecisionExact as Review

------------------------------------------------------------------------
-- Case review targets.
------------------------------------------------------------------------

data ReviewTarget : Set where
  fireWeaverIDFOperationalAuthority : ReviewTarget
  fireWeaverOCIProductIntegration : ReviewTarget
  ellisonFIDFDeclaredMotive : ReviewTarget
  berrebiKlorElectoralCausalSurface : ReviewTarget

record ReviewedPromotionCandidate (target : ReviewTarget) : Set where
  constructor reviewed-promotion-candidate
  field
    genericReview : Review.GenericHumanReviewReceipt
    exactBinding : Review.ExactReviewItemBinding
    sourceIdentityReference : String
    claimIdentityReference : String
    extractionReference : String
    promotionConsumerReference : String
    reviewScopeReference : String

open ReviewedPromotionCandidate public

------------------------------------------------------------------------
-- No review receipt is fabricated for the current externally acquired
-- evidence.  These flags describe current review-state payment only.
------------------------------------------------------------------------

fireWeaverAuthorityExactReviewPaid : Bool
fireWeaverAuthorityExactReviewPaid = false

fireWeaverOCIIntegrationExactReviewPaid : Bool
fireWeaverOCIIntegrationExactReviewPaid = false

ellisonFIDFMotiveExactReviewPaid : Bool
ellisonFIDFMotiveExactReviewPaid = false

berrebiKlorCausalExactReviewPaid : Bool
berrebiKlorCausalExactReviewPaid = false

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

sourceAcquisitionAutomaticallyPaysExactReview : Bool
sourceAcquisitionAutomaticallyPaysExactReview = false

exactReviewAutomaticallyPaysClaimTruth : Bool
exactReviewAutomaticallyPaysClaimTruth = false

exactReviewAutomaticallyPaysAuthorityPromotion : Bool
exactReviewAutomaticallyPaysAuthorityPromotion = false

exactReviewAutomaticallyPaysCausalIdentification : Bool
exactReviewAutomaticallyPaysCausalIdentification = false

exactReviewAutomaticallyPaysMotiveBeyondReviewedClaim : Bool
exactReviewAutomaticallyPaysMotiveBeyondReviewedClaim = false

reviewMetadataCanRebindDifferentSourceClaim : Bool
reviewMetadataCanRebindDifferentSourceClaim = false

------------------------------------------------------------------------
-- Literal reuse of master generic review boundaries.
------------------------------------------------------------------------

genericReviewRequiresExactItemBinding : Bool
genericReviewRequiresExactItemBinding = true

genericReviewCreatesClaimTruth : Bool
genericReviewCreatesClaimTruth = false

record ExactReviewPromotionBoundary : Set where
  constructor exact-review-promotion-boundary
  field
    sourceAndReviewAreSeparate : Bool
    exactSourceClaimBindingRequired : Bool
    reviewCreatesTruth : Bool
    reviewCreatesAuthority : Bool
    reviewCreatesCausalEffect : Bool
    reviewCreatesUnrelatedMotive : Bool
    currentCaseReviewReceiptsFabricated : Bool

canonicalExactReviewPromotionBoundary : ExactReviewPromotionBoundary
canonicalExactReviewPromotionBoundary =
  exact-review-promotion-boundary
    true true false false false false false
