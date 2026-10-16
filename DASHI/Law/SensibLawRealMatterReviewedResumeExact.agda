module DASHI.Law.SensibLawRealMatterReviewedResumeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawRealMatterReviewDecisionExact as Review

------------------------------------------------------------------------
-- REVIEWED REAL-MATTER RESUME
--
-- After the durable legal review decision, runtime may materialise the existing
-- reviewed-evidence coordinate, LegalIR, and derived/challengeable legal-follow
-- projection. REL still requires a second observation and explicit consumer
-- contract; this resume boundary must not invent either.
------------------------------------------------------------------------

selectedReviewBoundary : Review.RealMatterReviewBoundary
selectedReviewBoundary = Review.canonicalRealMatterReviewBoundary

record ReviewedRealMatterResume : Set where
  constructor reviewed-real-matter-resume
  field
    reviewDecisionRef : String
    reviewedEvidenceRef : String
    legalIrSemanticBuildRef : String
    legalIrProjectionRef : String
    legalIrObservationRef : String
    legalIrGraphRevisionRef : String
    legalFollowProjectionRef : String
    legalFollowSupportEdgeRef : String
    exactNativeSourceReopened : Bool
    exactNativeSourceReopenedIsTrue : exactNativeSourceReopened ≡ true
    reviewRoleExplicit : Bool
    reviewRoleExplicitIsTrue : reviewRoleExplicit ≡ true
    normativeOrderExplicit : Bool
    normativeOrderExplicitIsTrue : normativeOrderExplicit ≡ true
    legalFollowDerivedOnly : Bool
    legalFollowDerivedOnlyIsTrue : legalFollowDerivedOnly ≡ true
    legalFollowChallengeable : Bool
    legalFollowChallengeableIsTrue : legalFollowChallengeable ≡ true
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    createsLegalAuthority : Bool
    createsLegalAuthorityIsFalse : createsLegalAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open ReviewedRealMatterResume public

record ReviewedResumeBoundary : Set where
  constructor reviewed-resume-boundary
  field
    durableReviewDecisionRequired : Bool
    durableReviewDecisionRequiredIsTrue : durableReviewDecisionRequired ≡ true
    reviewedEvidenceMayMaterialise : Bool
    reviewedEvidenceMayMaterialiseIsTrue : reviewedEvidenceMayMaterialise ≡ true
    legalIrMayMaterialise : Bool
    legalIrMayMaterialiseIsTrue : legalIrMayMaterialise ≡ true
    derivedLegalFollowMayMaterialise : Bool
    derivedLegalFollowMayMaterialiseIsTrue : derivedLegalFollowMayMaterialise ≡ true
    relationalComparisonAutomaticallyCreated : Bool
    relationalComparisonAutomaticallyCreatedIsFalse :
      relationalComparisonAutomaticallyCreated ≡ false
    secondObservationAutomaticallyChosen : Bool
    secondObservationAutomaticallyChosenIsFalse : secondObservationAutomaticallyChosen ≡ false
    relationalConsumerAutomaticallyChosen : Bool
    relationalConsumerAutomaticallyChosenIsFalse : relationalConsumerAutomaticallyChosen ≡ false

open ReviewedResumeBoundary public

canonicalReviewedResumeBoundary : ReviewedResumeBoundary
canonicalReviewedResumeBoundary =
  reviewed-resume-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

data ReviewedEvidenceEqualsRelComparison : Set where
data LegalFollowProjectionEqualsRelComparison : Set where
data ReviewDecisionSelectsSecondObservation : Set where
data ReviewDecisionSelectsRelConsumer : Set where

reviewedEvidenceDoesNotEqualRelComparison : ReviewedEvidenceEqualsRelComparison → ⊥
reviewedEvidenceDoesNotEqualRelComparison ()

legalFollowProjectionDoesNotEqualRelComparison : LegalFollowProjectionEqualsRelComparison → ⊥
legalFollowProjectionDoesNotEqualRelComparison ()

reviewDecisionDoesNotSelectSecondObservation : ReviewDecisionSelectsSecondObservation → ⊥
reviewDecisionDoesNotSelectSecondObservation ()

reviewDecisionDoesNotSelectRelConsumer : ReviewDecisionSelectsRelConsumer → ⊥
reviewDecisionDoesNotSelectRelConsumer ()
