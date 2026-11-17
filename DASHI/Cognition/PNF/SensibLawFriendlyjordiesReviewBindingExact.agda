module DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewBindingExact where

------------------------------------------------------------------------
-- SAME-PROPOSITION REVIEW BINDING
--
-- REAL-MATTER deliberately keeps the generic human-review receipt and exact
-- source/candidate binding as separate reusable objects.  For this governance
-- application, join them explicitly at the proposition/bundle boundary rather
-- than treating adjacency as identity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.FriendlyjordiesGovernanceQuestionExact as March
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesWorldEvidenceExact as World
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedWorldEvidenceExact as Reviewed
import DASHI.Law.SensibLawRealMatterReviewDecisionExact as Review

reviewReceiptAndBindingSameProposition : Bool
reviewReceiptAndBindingSameProposition = true

record SamePropositionReviewedWorldEvidenceDecision
    (case : March.MarchCase)
    (bundle : World.ExternalWorldFactBundle case) : Set₁ where
  constructor same-proposition-reviewed-world-evidence-decision
  field
    decision : Reviewed.ReviewedWorldEvidenceDecision case bundle

    reviewObservationMatchesProposition :
      Review.GenericHumanReviewReceipt.observationRef
        (Reviewed.ReviewedWorldEvidenceDecision.genericReview decision)
      ≡ Reviewed.ReviewedWorldEvidenceDecision.propositionRef decision

    bindingFactorMatchesProposition :
      Review.ExactReviewItemBinding.candidateFactorRef
        (Reviewed.ReviewedWorldEvidenceDecision.exactReviewBinding decision)
      ≡ Reviewed.ReviewedWorldEvidenceDecision.propositionRef decision

    bindingSourceMatchesBundle :
      Review.ExactReviewItemBinding.sourceManifestationRef
        (Reviewed.ReviewedWorldEvidenceDecision.exactReviewBinding decision)
      ≡ Reviewed.ReviewedWorldEvidenceDecision.bundleRef decision

    samePropositionBindingCreatesTruth : Bool
    samePropositionBindingCreatesTruthIsFalse :
      samePropositionBindingCreatesTruth ≡ false

open SamePropositionReviewedWorldEvidenceDecision public

acceptedOrQualifiedStillRequired :
  ∀ {case : March.MarchCase}
    {bundle : World.ExternalWorldFactBundle case}
    (bound : SamePropositionReviewedWorldEvidenceDecision case bundle) →
  Review.ExactReviewItemBinding.acceptedOrQualified
    (Reviewed.ReviewedWorldEvidenceDecision.exactReviewBinding
      (decision bound)) ≡ true
acceptedOrQualifiedStillRequired bound =
  Reviewed.reviewedDecisionRetainsAcceptedOrQualified (decision bound)

record FriendlyjordiesReviewBindingBoundary : Set where
  constructor friendlyjordies-review-binding-boundary
  field
    genericObservationAndBoundFactorShareProposition : Bool
    genericObservationAndBoundFactorSharePropositionIsTrue :
      genericObservationAndBoundFactorShareProposition ≡ true
    exactBindingSourceMatchesReviewedBundle : Bool
    exactBindingSourceMatchesReviewedBundleIsTrue :
      exactBindingSourceMatchesReviewedBundle ≡ true
    bindingCreatesClaimTruth : Bool
    bindingCreatesClaimTruthIsFalse : bindingCreatesClaimTruth ≡ false

canonicalFriendlyjordiesReviewBindingBoundary :
  FriendlyjordiesReviewBindingBoundary
canonicalFriendlyjordiesReviewBindingBoundary =
  friendlyjordies-review-binding-boundary
    true refl
    true refl
    false refl
