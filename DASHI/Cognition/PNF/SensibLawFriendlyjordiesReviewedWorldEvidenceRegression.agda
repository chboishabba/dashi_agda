module DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedWorldEvidenceRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.HumanReviewCore as Review
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedWorldEvidenceExact as Reviewed

reusesGenericHumanReviewReceipt :
  Reviewed.genericHumanReviewReceiptReused ≡ true
reusesGenericHumanReviewReceipt = refl

reusesExactReviewItemBinding :
  Reviewed.exactReviewItemBindingReused ≡ true
reusesExactReviewItemBinding = refl

reviewMetadataAloneCreatesCausation :
  Reviewed.reviewMetadataAloneCreatesCausalPremise ≡ false
reviewMetadataAloneCreatesCausation = refl

reviewedCausalBridgeCreatesPartyRanking :
  Reviewed.reviewedBridgeCreatesUniversalPartyRanking ≡ false
reviewedCausalBridgeCreatesPartyRanking = refl

humanReviewDoesNotCreateClaimTruth :
  Review.HumanReviewCoreBoundary.reviewCreatesClaimTruth
    Review.canonicalHumanReviewCoreBoundary ≡ false
humanReviewDoesNotCreateClaimTruth =
  Reviewed.humanReviewCoreDoesNotCreateClaimTruth

humanReviewDoesNotIdentifyCause :
  Review.HumanReviewCoreBoundary.reviewCreatesCausalIdentification
    Review.canonicalHumanReviewCoreBoundary ≡ false
humanReviewDoesNotIdentifyCause =
  Reviewed.humanReviewCoreDoesNotCreateCausalIdentification
