module DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedWorldEvidenceRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.FriendlyjordiesGovernanceQuestionExact as March
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesWorldEvidenceExact as World
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedWorldEvidenceExact as Reviewed
import DASHI.Law.SensibLawRealMatterReviewDecisionExact as Review

reusesGenericHumanReviewReceipt :
  Reviewed.genericHumanReviewReceiptReused ≡ true
reusesGenericHumanReviewReceipt = refl

reusesExactReviewItemBinding :
  Reviewed.exactReviewItemBindingReused ≡ true
reusesExactReviewItemBinding = refl

legalEvidenceDecisionRequired :
  Reviewed.legalEvidenceDecisionRequiredForHistoricalReview ≡ false
legalEvidenceDecisionRequired = refl

reviewMetadataAloneCreatesCausation :
  Reviewed.reviewMetadataAloneCreatesCausalPremise ≡ false
reviewMetadataAloneCreatesCausation = refl

reviewedCausalBridgeCreatesPartyRanking :
  Reviewed.reviewedBridgeCreatesUniversalPartyRanking ≡ false
reviewedCausalBridgeCreatesPartyRanking = refl

acceptedOrQualifiedReceiptSurvives :
  (decision :
    Reviewed.ReviewedWorldEvidenceDecision
      March.cprs2009
      World.cprsExternalWorldBundle) →
  Review.ExactReviewItemBinding.acceptedOrQualified
    (Reviewed.ReviewedWorldEvidenceDecision.exactReviewBinding decision)
  ≡ true
acceptedOrQualifiedReceiptSurvives =
  Reviewed.reviewedDecisionRetainsAcceptedOrQualified
