module DASHI.Wikimedia.Mabo100HopReviewedCampaignValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Wikimedia.Mabo100HopReviewedCampaignExact

validationHopBudget : campaignHopBudget ≡ 100
validationHopBudget = refl

validationManifestRequired :
  reviewManifestRequired canonicalReviewedCampaignBoundary ≡ true
validationManifestRequired = refl

validationDiagnosisDoesNotEqualReview :
  diagnosisProposalEqualsIdentityReview canonicalReviewedCampaignBoundary ≡ false
validationDiagnosisDoesNotEqualReview = refl

validationReviewDoesNotEqualPayment :
  identityReviewEqualsPersistedPayment canonicalReviewedCampaignBoundary ≡ false
validationReviewDoesNotEqualPayment = refl

validationPaymentDoesNotEqualNovelAdmission :
  persistedPaymentEqualsNovelDurableAdmission canonicalReviewedCampaignBoundary ≡ false
validationPaymentDoesNotEqualNovelAdmission = refl

validationKnownIdentityPaymentNonNovel :
  knownIdentityPaymentCountsNovel canonicalReviewedCampaignBoundary ≡ false
validationKnownIdentityPaymentNonNovel = refl

validationMissingCarrierCannotManufactureValue :
  missingCarrierAnalysisCreatesMissingValue canonicalReviewedCampaignBoundary ≡ false
validationMissingCarrierCannotManufactureValue = refl

validationExternalComparisonCannotReview :
  externalKnowledgeComparisonCreatesIdentityReview canonicalReviewedCampaignBoundary ≡ false
validationExternalComparisonCannotReview = refl

validationSfmCannotReview :
  semiFormalPresentationCreatesIdentityReview canonicalReviewedCampaignBoundary ≡ false
validationSfmCannotReview = refl

validationWrongTypeFailsClosed :
  wrongTypeFailsClosed canonicalReviewedCampaignBoundary ≡ true
validationWrongTypeFailsClosed = refl

validationCandidateOnly :
  campaignCandidateOnly canonicalReviewedCampaignBoundary ≡ true
validationCandidateOnly = refl

validationNoAuthority :
  campaignCreatesSemanticAuthority canonicalReviewedCampaignBoundary ≡ false
validationNoAuthority = refl

validationNoApplicability :
  campaignApplicabilityPromoted canonicalReviewedCampaignBoundary ≡ false
validationNoApplicability = refl

validationNoTruth :
  campaignClaimTruthPromoted canonicalReviewedCampaignBoundary ≡ false
validationNoTruth = refl
