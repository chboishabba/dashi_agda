module DASHI.Law.RevisionReReviewPropagationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Law.LegalWorldRevisionReconstructionExact as World

------------------------------------------------------------------------
-- S18.7/S18.8: revision invalidation -> explicit re-review/recompute plan.
--
-- Direct source dependents require evidence re-review; transitive dependents
-- require recomputation.  Neither operation decides the new proposition truth.
------------------------------------------------------------------------

data ReReviewKind : Set where
  reacquireChangedSource : ReReviewKind
  rereviewDirectEvidence : ReReviewKind
  recomputeDependentProof : ReReviewKind

data Artifact : Set where
  changedSource directProposition dependentProposition consumerProof : Artifact

data Depends : Artifact → Artifact → Set where
  sourceDirect : Depends changedSource directProposition
  directDependent : Depends directProposition dependentProposition
  dependentProof : Depends dependentProposition consumerProof

directReopening :
  Dependency.ReopeningObligation Depends changedSource directProposition
directReopening =
  Dependency.oneEdgeCreatesReopeningObligation sourceDirect

dependentReopening :
  Dependency.ReopeningObligation Depends changedSource dependentProposition
dependentReopening =
  Dependency.obligationsCompose
    directReopening
    (Dependency.oneEdgeCreatesReopeningObligation directDependent)

proofReopening :
  Dependency.ReopeningObligation Depends changedSource consumerProof
proofReopening =
  Dependency.obligationsCompose
    dependentReopening
    (Dependency.oneEdgeCreatesReopeningObligation dependentProof)

rereviewKind : Artifact → ReReviewKind
rereviewKind changedSource = reacquireChangedSource
rereviewKind directProposition = rereviewDirectEvidence
rereviewKind dependentProposition = recomputeDependentProof
rereviewKind consumerProof = recomputeDependentProof

directNeedsEvidenceReview :
  rereviewKind directProposition ≡ rereviewDirectEvidence
directNeedsEvidenceReview = refl

proofNeedsRecompute :
  rereviewKind consumerProof ≡ recomputeDependentProof
proofNeedsRecompute = refl

data ReReviewAutomaticallyNewTruth : Set where
data RecomputeAutomaticallyNewTruth : Set where

rereviewDoesNotDecideNewTruth :
  ReReviewAutomaticallyNewTruth → ⊥
rereviewDoesNotDecideNewTruth ()

recomputeDoesNotDecideNewTruth :
  RecomputeAutomaticallyNewTruth → ⊥
recomputeDoesNotDecideNewTruth ()

worldRevisionBoundary :
  World.LegalWorldRevisionReconstructionBoundary
worldRevisionBoundary =
  World.canonicalLegalWorldRevisionReconstructionBoundary

record RevisionReReviewPropagationBoundary : Set where
  constructor revisionReReviewPropagationBoundary
  field
    changedSourceRequiresReacquisition : Bool
    changedSourceRequiresReacquisitionIsTrue :
      changedSourceRequiresReacquisition ≡ true

    directDependentRequiresEvidenceReview : Bool
    directDependentRequiresEvidenceReviewIsTrue :
      directDependentRequiresEvidenceReview ≡ true

    transitiveDependentRequiresRecomputation : Bool
    transitiveDependentRequiresRecomputationIsTrue :
      transitiveDependentRequiresRecomputation ≡ true

    rereviewAutomaticallyChangesClaimTruth : Bool
    rereviewAutomaticallyChangesClaimTruthIsFalse :
      rereviewAutomaticallyChangesClaimTruth ≡ false

    recomputationAutomaticallyChangesClaimTruth : Bool
    recomputationAutomaticallyChangesClaimTruthIsFalse :
      recomputationAutomaticallyChangesClaimTruth ≡ false

open RevisionReReviewPropagationBoundary public

canonicalRevisionReReviewPropagationBoundary :
  RevisionReReviewPropagationBoundary
canonicalRevisionReReviewPropagationBoundary =
  revisionReReviewPropagationBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
