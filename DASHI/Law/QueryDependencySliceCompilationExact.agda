module DASHI.Law.QueryDependencySliceCompilationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- S15: compile query dependency slices from explanation/provenance structure.
--
-- The finite witness models the runtime owner:
--
--   required proposition
--        ↓ depends on
--   reviewed evidence
--        ↓ depends on
--   source revision
--
-- An unrelated source has no dependency path into Q and therefore must not be
-- admitted merely because it exists elsewhere in the same world/projection.
------------------------------------------------------------------------

data Ref : Set where
  queryProposition reviewedEvidence sourceRevision unrelatedSource : Ref

data DependsOn : Ref → Ref → Set where
  queryDependsOnReview :
    DependsOn queryProposition reviewedEvidence
  reviewDependsOnRevision :
    DependsOn reviewedEvidence sourceRevision

data DependencyPath : Ref → Ref → Set where
  here :
    ∀ {x} →
    DependencyPath x x
  step :
    ∀ {x y z} →
    DependsOn x y →
    DependencyPath y z →
    DependencyPath x z

queryContainsReviewedEvidence :
  DependencyPath queryProposition reviewedEvidence
queryContainsReviewedEvidence =
  step queryDependsOnReview here

queryContainsSourceRevision :
  DependencyPath queryProposition sourceRevision
queryContainsSourceRevision =
  step queryDependsOnReview
    (step reviewDependsOnRevision here)

sourceRevisionHasNoOutgoingDependency :
  ∀ {target} →
  DependsOn sourceRevision target →
  ⊥
sourceRevisionHasNoOutgoingDependency ()

reviewedEvidenceCannotReachUnrelated :
  DependencyPath reviewedEvidence unrelatedSource →
  ⊥
reviewedEvidenceCannotReachUnrelated
  (step reviewDependsOnRevision path) with path
... | ()

queryCannotReachUnrelated :
  DependencyPath queryProposition unrelatedSource →
  ⊥
queryCannotReachUnrelated
  (step queryDependsOnReview path) =
    reviewedEvidenceCannotReachUnrelated path

data SliceMembership : Ref → Set where
  requiredSemanticMember :
    SliceMembership queryProposition
  transitiveReviewMember :
    SliceMembership reviewedEvidence
  provenanceRevisionMember :
    SliceMembership sourceRevision

querySemanticIsInSlice :
  SliceMembership queryProposition
querySemanticIsInSlice =
  requiredSemanticMember

reviewDependencyIsInSlice :
  SliceMembership reviewedEvidence
reviewDependencyIsInSlice =
  transitiveReviewMember

sourceRevisionIsInSlice :
  SliceMembership sourceRevision
sourceRevisionIsInSlice =
  provenanceRevisionMember

data UnrelatedSourceAutomaticallyInSlice : Set where

unrelatedSourceCannotEnterWithoutDependencyPath :
  UnrelatedSourceAutomaticallyInSlice → ⊥
unrelatedSourceCannotEnterWithoutDependencyPath ()

record QueryDependencySliceCompilationBoundary : Set where
  constructor queryDependencySliceCompilationBoundary
  field
    requiredSemanticRefSeedsSlice : Bool
    requiredSemanticRefSeedsSliceIsTrue :
      requiredSemanticRefSeedsSlice ≡ true

    transitiveExplanationDependencyEntersSlice : Bool
    transitiveExplanationDependencyEntersSliceIsTrue :
      transitiveExplanationDependencyEntersSlice ≡ true

    provenanceSourceRevisionEntersSlice : Bool
    provenanceSourceRevisionEntersSliceIsTrue :
      provenanceSourceRevisionEntersSlice ≡ true

    unrelatedWorldSourceAutomaticallyEntersSlice : Bool
    unrelatedWorldSourceAutomaticallyEntersSliceIsFalse :
      unrelatedWorldSourceAutomaticallyEntersSlice ≡ false

    sliceCompilationCreatesSemanticAuthority : Bool
    sliceCompilationCreatesSemanticAuthorityIsFalse :
      sliceCompilationCreatesSemanticAuthority ≡ false

    sliceCompilationCreatesClaimTruth : Bool
    sliceCompilationCreatesClaimTruthIsFalse :
      sliceCompilationCreatesClaimTruth ≡ false

open QueryDependencySliceCompilationBoundary public

canonicalQueryDependencySliceCompilationBoundary :
  QueryDependencySliceCompilationBoundary
canonicalQueryDependencySliceCompilationBoundary =
  queryDependencySliceCompilationBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
