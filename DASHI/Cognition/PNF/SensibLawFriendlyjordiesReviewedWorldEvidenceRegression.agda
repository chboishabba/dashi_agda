module DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedWorldEvidenceRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedWorldEvidenceExact as Reviewed

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
