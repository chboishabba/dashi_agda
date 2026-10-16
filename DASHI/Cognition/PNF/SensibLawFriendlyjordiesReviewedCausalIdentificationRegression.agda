module DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedCausalIdentificationRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedCausalIdentificationExact as Reviewed

reviewReceiptRequiredAfterIdentification :
  Reviewed.reviewReceiptRequiredAfterIdentification ≡ true
reviewReceiptRequiredAfterIdentification = refl

exactReviewBindingRequired :
  Reviewed.exactReviewBindingRequired ≡ true
exactReviewBindingRequired = refl

reviewDoesNotReplaceIdentification :
  Reviewed.reviewReceiptReplacesIdentificationGate ≡ false
reviewDoesNotReplaceIdentification = refl

identificationDoesNotReplaceReview :
  Reviewed.identificationGateReplacesReviewReceipt ≡ false
identificationDoesNotReplaceReview = refl

reviewedIdentificationCreatesRanking :
  Reviewed.reviewedIdentificationCreatesUniversalPartyRanking ≡ false
reviewedIdentificationCreatesRanking = refl

southAustraliaStillNeedsNarrativeSource :
  Reviewed.southAustraliaNarrativeSourceStillIndependent ≡ true
southAustraliaStillNeedsNarrativeSource = refl
