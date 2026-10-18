module DASHI.Wikimedia.MaboConsumerResidualDiagnosisValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Wikimedia.MaboConsumerResidualDiagnosisExact

validationHopBudget : requestedHopBudget ≡ 100
validationHopBudget = refl

validationProofSearchProposalOnly :
  proposalOnly proofSearchDiagnosisRoute ≡ true
validationProofSearchProposalOnly = refl

validationExperimentProposalOnly :
  proposalOnly experimentalDesignDiagnosisRoute ≡ true
validationExperimentProposalOnly = refl

validationWrongTypeCanReject :
  wrongTypeCanReject wrongTypeDiagnosisRoute ≡ true
validationWrongTypeCanReject = refl

validationExternalComparisonCannotPay :
  selfCertifiesPayment externalKnowledgeDiagnosisRoute ≡ false
validationExternalComparisonCannotPay = refl

validationContextReviewDoesNotPayIdentityReview :
  contextReviewPaysIdentityReview canonicalDiagnosisBoundary ≡ false
validationContextReviewDoesNotPayIdentityReview = refl

validationAdjacencyDoesNotCreateRequirement :
  arbitraryAdjacencyCreatesConsumerRequirement canonicalDiagnosisBoundary ≡ false
validationAdjacencyDoesNotCreateRequirement = refl

validationKnownIdentityQuotientedFirst :
  durableKnownIdentityQuotientedBeforeResidual canonicalDiagnosisBoundary ≡ true
validationKnownIdentityQuotientedFirst = refl

validationCandidateOnly : candidateOnly canonicalDiagnosisBoundary ≡ true
validationCandidateOnly = refl

validationNoAuthority : createsSemanticAuthority canonicalDiagnosisBoundary ≡ false
validationNoAuthority = refl

validationNoApplicability : applicabilityPromoted canonicalDiagnosisBoundary ≡ false
validationNoApplicability = refl

validationNoTruth : claimTruthPromoted canonicalDiagnosisBoundary ≡ false
validationNoTruth = refl
