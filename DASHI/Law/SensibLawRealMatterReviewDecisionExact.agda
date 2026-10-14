module DASHI.Law.SensibLawRealMatterReviewDecisionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.HumanReviewCore as HumanReview
import DASHI.Law.SensibLawProviderPinnedEphemeralMaterialisationExact as Source

-- Preserve the historical SensibLaw API while moving the generic carriers to
-- Core. Existing downstream users may continue to refer to
-- Review.GenericHumanReviewReceipt / Review.ExactReviewItemBinding and their
-- constructors/projections without acquiring a new legal-specific type.
open HumanReview public

------------------------------------------------------------------------
-- REAL-MATTER-1 REVIEW DECISION
--
-- Source materialisation and candidate PNF do not pay review. The generic human
-- review carriers are now owned by DASHI.Core.HumanReviewCore. This legal owner
-- adds only the domain-specific evidence-role and normative-order decision.
------------------------------------------------------------------------

selectedSourceBoundary : Source.ProviderCandidatePnfBoundary
selectedSourceBoundary = Source.canonicalProviderCandidatePnfBoundary

record LegalEvidenceReviewDecision : Set where
  constructor legal-evidence-review-decision
  field
    genericReview : GenericHumanReviewReceipt
    exactReviewItemBinding : ExactReviewItemBinding
    requirementRef : String
    evidenceRoleRef : String
    normativeOrderRef : String
    propositionRef : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open LegalEvidenceReviewDecision public

record RealMatterReviewBoundary : Set where
  constructor real-matter-review-boundary
  field
    exactSourceAndCandidateRequiredBeforeReview : Bool
    exactSourceAndCandidateRequiredBeforeReviewIsTrue :
      exactSourceAndCandidateRequiredBeforeReview ≡ true
    genericHumanReviewReceiptRequired : Bool
    genericHumanReviewReceiptRequiredIsTrue : genericHumanReviewReceiptRequired ≡ true
    exactReviewItemProvenanceRequired : Bool
    exactReviewItemProvenanceRequiredIsTrue : exactReviewItemProvenanceRequired ≡ true
    sameObservationReceiptMayRebindDifferentCandidate : Bool
    sameObservationReceiptMayRebindDifferentCandidateIsFalse :
      sameObservationReceiptMayRebindDifferentCandidate ≡ false
    evidenceRoleRequiresDurableDecision : Bool
    evidenceRoleRequiresDurableDecisionIsTrue : evidenceRoleRequiresDurableDecision ≡ true
    normativeOrderRequiresDurableDecision : Bool
    normativeOrderRequiresDurableDecisionIsTrue : normativeOrderRequiresDurableDecision ≡ true
    downstreamMayRestateEvidenceRole : Bool
    downstreamMayRestateEvidenceRoleIsFalse : downstreamMayRestateEvidenceRole ≡ false
    downstreamMayRestateNormativeOrder : Bool
    downstreamMayRestateNormativeOrderIsFalse : downstreamMayRestateNormativeOrder ≡ false
    reviewDecisionPromotesApplicability : Bool
    reviewDecisionPromotesApplicabilityIsFalse : reviewDecisionPromotesApplicability ≡ false
    reviewDecisionPromotesClaimTruth : Bool
    reviewDecisionPromotesClaimTruthIsFalse : reviewDecisionPromotesClaimTruth ≡ false

open RealMatterReviewBoundary public

canonicalRealMatterReviewBoundary : RealMatterReviewBoundary
canonicalRealMatterReviewBoundary =
  real-matter-review-boundary
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data GenericReviewReceiptEqualsLegalEvidenceDecision : Set where
data CandidatePnfPaysLegalReviewDecision : Set where
data SameObservationReceiptMayRebindDifferentCandidate : Set where
data DownstreamMayRestateEvidenceRole : Set where
data DownstreamMayRestateNormativeOrder : Set where
data LegalReviewDecisionCreatesApplicability : Set where
data LegalReviewDecisionCreatesClaimTruth : Set where

genericReviewReceiptDoesNotEqualLegalEvidenceDecision :
  GenericReviewReceiptEqualsLegalEvidenceDecision → ⊥
genericReviewReceiptDoesNotEqualLegalEvidenceDecision ()

candidatePnfDoesNotPayLegalReviewDecision :
  CandidatePnfPaysLegalReviewDecision → ⊥
candidatePnfDoesNotPayLegalReviewDecision ()

sameObservationReceiptCannotRebindDifferentCandidate :
  SameObservationReceiptMayRebindDifferentCandidate → ⊥
sameObservationReceiptCannotRebindDifferentCandidate ()

downstreamCannotRestateEvidenceRole : DownstreamMayRestateEvidenceRole → ⊥
downstreamCannotRestateEvidenceRole ()

downstreamCannotRestateNormativeOrder : DownstreamMayRestateNormativeOrder → ⊥
downstreamCannotRestateNormativeOrder ()

legalReviewDecisionDoesNotCreateApplicability :
  LegalReviewDecisionCreatesApplicability → ⊥
legalReviewDecisionDoesNotCreateApplicability ()

legalReviewDecisionDoesNotCreateClaimTruth :
  LegalReviewDecisionCreatesClaimTruth → ⊥
legalReviewDecisionDoesNotCreateClaimTruth ()
