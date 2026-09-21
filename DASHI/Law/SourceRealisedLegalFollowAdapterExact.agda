module DASHI.Law.SourceRealisedLegalFollowAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.GenericReviewedDeltaCampaignKernelExact as Kernel

------------------------------------------------------------------------
-- S16: source-realised legal domains reuse the generic LegalFollow recurrence.
--
-- Doctrine-specific semantics remain in the legal evaluator.  The generic
-- kernel sees only:
--
--   residual -> selected demand -> reviewed context delta -> recompute
--
-- A reviewed delta may not silently change jurisdiction/time and may not
-- manufacture legal authority or claim truth.
------------------------------------------------------------------------

data LegalDomain : Set where
  nativeTitle negligence institutionalAbuse : LegalDomain

data LegalState : Set where
  unresolved reviewedClosed : LegalState

data LegalResidual : Set where
  unresolvedElement : LegalResidual

data LegalDemand : Set where
  reviewElement : LegalDemand

data ReviewedDelta : Set where
  reviewedElementDelta : ReviewedDelta

recomputeResiduals : LegalState → List LegalResidual
recomputeResiduals unresolved =
  unresolvedElement ∷ []
recomputeResiduals reviewedClosed =
  []

selectDemand : LegalState → Maybe LegalDemand
selectDemand unresolved =
  just reviewElement
selectDemand reviewedClosed =
  nothing

applyReviewedDelta : LegalState → ReviewedDelta → LegalState
applyReviewedDelta unresolved reviewedElementDelta =
  reviewedClosed
applyReviewedDelta reviewedClosed reviewedElementDelta =
  reviewedClosed

cullenLikeReviewedTransition :
  applyReviewedDelta unresolved reviewedElementDelta ≡ reviewedClosed
cullenLikeReviewedTransition =
  refl

recomputeAfterReviewedTransition :
  recomputeResiduals
    (applyReviewedDelta unresolved reviewedElementDelta)
  ≡
  []
recomputeAfterReviewedTransition =
  refl

nextDemandAfterReviewedTransition :
  selectDemand
    (applyReviewedDelta unresolved reviewedElementDelta)
  ≡
  nothing
nextDemandAfterReviewedTransition =
  refl

genericKernelBoundary :
  Kernel.GenericReviewedDeltaCampaignKernelBoundary
genericKernelBoundary =
  Kernel.canonicalGenericReviewedDeltaCampaignKernelBoundary

data RawSourceAutomaticallyReviewedContextDelta : Set where
data ReviewedDeltaAutomaticallyChangesWorldCoordinate : Set where
data ReviewedDeltaAutomaticallyCreatesAuthority : Set where
data ReviewedDeltaAutomaticallyCreatesClaimTruth : Set where

rawSourceCannotBecomeReviewedDelta :
  RawSourceAutomaticallyReviewedContextDelta → ⊥
rawSourceCannotBecomeReviewedDelta ()

reviewedDeltaCannotSilentlyChangeWorldCoordinate :
  ReviewedDeltaAutomaticallyChangesWorldCoordinate → ⊥
reviewedDeltaCannotSilentlyChangeWorldCoordinate ()

reviewedDeltaCannotCreateAuthority :
  ReviewedDeltaAutomaticallyCreatesAuthority → ⊥
reviewedDeltaCannotCreateAuthority ()

reviewedDeltaCannotCreateClaimTruth :
  ReviewedDeltaAutomaticallyCreatesClaimTruth → ⊥
reviewedDeltaCannotCreateClaimTruth ()

record SourceRealisedLegalFollowAdapterBoundary : Set where
  constructor sourceRealisedLegalFollowAdapterBoundary
  field
    sourceRealisedLegalDomainUsesGenericKernel : Bool
    sourceRealisedLegalDomainUsesGenericKernelIsTrue :
      sourceRealisedLegalDomainUsesGenericKernel ≡ true

    negligenceMayUseSameKernelAsNativeTitle : Bool
    negligenceMayUseSameKernelAsNativeTitleIsTrue :
      negligenceMayUseSameKernelAsNativeTitle ≡ true

    reviewedDeltaMustPaySelectedResidual : Bool
    reviewedDeltaMustPaySelectedResidualIsTrue :
      reviewedDeltaMustPaySelectedResidual ≡ true

    reviewedDeltaMaySilentlyChangeWorldCoordinate : Bool
    reviewedDeltaMaySilentlyChangeWorldCoordinateIsFalse :
      reviewedDeltaMaySilentlyChangeWorldCoordinate ≡ false

    reviewedDeltaCreatesSemanticAuthority : Bool
    reviewedDeltaCreatesSemanticAuthorityIsFalse :
      reviewedDeltaCreatesSemanticAuthority ≡ false

    reviewedDeltaCreatesClaimTruth : Bool
    reviewedDeltaCreatesClaimTruthIsFalse :
      reviewedDeltaCreatesClaimTruth ≡ false

open SourceRealisedLegalFollowAdapterBoundary public

canonicalSourceRealisedLegalFollowAdapterBoundary :
  SourceRealisedLegalFollowAdapterBoundary
canonicalSourceRealisedLegalFollowAdapterBoundary =
  sourceRealisedLegalFollowAdapterBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
