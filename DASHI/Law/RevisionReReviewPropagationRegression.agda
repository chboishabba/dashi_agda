module DASHI.Law.RevisionReReviewPropagationRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.RevisionReReviewPropagationExact as ReReview

boundary : ReReview.RevisionReReviewPropagationBoundary
boundary = ReReview.canonicalRevisionReReviewPropagationBoundary

sourceReacquire :
  ReReview.changedSourceRequiresReacquisition boundary ≡ true
sourceReacquire =
  ReReview.changedSourceRequiresReacquisitionIsTrue boundary

directReview :
  ReReview.directDependentRequiresEvidenceReview boundary ≡ true
directReview =
  ReReview.directDependentRequiresEvidenceReviewIsTrue boundary

transitiveRecompute :
  ReReview.transitiveDependentRequiresRecomputation boundary ≡ true
transitiveRecompute =
  ReReview.transitiveDependentRequiresRecomputationIsTrue boundary

reviewCreatesNoTruth :
  ReReview.rereviewAutomaticallyChangesClaimTruth boundary ≡ false
reviewCreatesNoTruth =
  ReReview.rereviewAutomaticallyChangesClaimTruthIsFalse boundary
