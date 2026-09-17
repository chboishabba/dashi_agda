module DASHI.Wikimedia.MaboReviewedEvidencePaymentValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Wikimedia.MaboReviewedEvidencePaymentExact

validationReviewCandidateOnly : candidateOnly maboParticipantIdentityReview ≡ true
validationReviewCandidateOnly = refl

validationReviewNoAuthority : createsSemanticAuthority maboParticipantIdentityReview ≡ false
validationReviewNoAuthority = refl

validationReviewNoApplicability : applicabilityPromoted maboParticipantIdentityReview ≡ false
validationReviewNoApplicability = refl

validationReviewNoTruth : claimTruthPromoted maboParticipantIdentityReview ≡ false
validationReviewNoTruth = refl

validationIdentityRequirementPaid : requirementsPaid maboParticipantIdentityPayment ≡ 1
validationIdentityRequirementPaid = refl

validationIdentityRequirementNoLongerUnpaid : requirementsUnpaid maboParticipantIdentityPayment ≡ 0
validationIdentityRequirementNoLongerUnpaid = refl

validationPaymentNoAuthority : paymentCreatesSemanticAuthority maboParticipantIdentityPayment ≡ false
validationPaymentNoAuthority = refl

validationPaymentNoApplicability : paymentPromotesApplicability maboParticipantIdentityPayment ≡ false
validationPaymentNoApplicability = refl

validationPaymentNoTruth : paymentPromotesClaimTruth maboParticipantIdentityPayment ≡ false
validationPaymentNoTruth = refl
