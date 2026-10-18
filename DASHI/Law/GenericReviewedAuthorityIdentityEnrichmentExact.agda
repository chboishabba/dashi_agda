module DASHI.Law.GenericReviewedAuthorityIdentityEnrichmentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Reviewed authority identity enrichment.
--
-- Acquisition metadata may omit an identity coordinate such as decision date.
-- Explicit review may pay that missing coordinate from retained source evidence.
-- Review enrichment is not authority promotion and may not silently contradict
-- a non-empty source coordinate.
------------------------------------------------------------------------

record ReviewedAuthorityIdentityEnrichmentBoundary : Set where
  constructor reviewedAuthorityIdentityEnrichmentBoundary
  field
    reviewMaySupplyMissingDecisionDate : Bool
    reviewMaySupplyMissingDecisionDateIsTrue :
      reviewMaySupplyMissingDecisionDate ≡ true

    reviewedDatePersistsIntoTraceNode : Bool
    reviewedDatePersistsIntoTraceNodeIsTrue :
      reviewedDatePersistsIntoTraceNode ≡ true

    reviewedDateMaySilentlyContradictSourceDate : Bool
    reviewedDateMaySilentlyContradictSourceDateIsFalse :
      reviewedDateMaySilentlyContradictSourceDate ≡ false

    sourceReceiptIsMutatedByReview : Bool
    sourceReceiptIsMutatedByReviewIsFalse :
      sourceReceiptIsMutatedByReview ≡ false

    reviewEnrichmentCreatesLegalAuthority : Bool
    reviewEnrichmentCreatesLegalAuthorityIsFalse :
      reviewEnrichmentCreatesLegalAuthority ≡ false

    reviewEnrichmentCreatesCurrentLawConclusion : Bool
    reviewEnrichmentCreatesCurrentLawConclusionIsFalse :
      reviewEnrichmentCreatesCurrentLawConclusion ≡ false

open ReviewedAuthorityIdentityEnrichmentBoundary public

canonicalReviewedAuthorityIdentityEnrichmentBoundary :
  ReviewedAuthorityIdentityEnrichmentBoundary
canonicalReviewedAuthorityIdentityEnrichmentBoundary =
  reviewedAuthorityIdentityEnrichmentBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

data ReviewedDateMayOverrideConflictingSourceDate : Set where
data ReviewEnrichmentAutomaticallyAuthority : Set where
data ReviewEnrichmentAutomaticallyCurrentLaw : Set where

reviewedDateCannotOverrideConflictingSourceDate :
  ReviewedDateMayOverrideConflictingSourceDate → ⊥
reviewedDateCannotOverrideConflictingSourceDate ()

reviewEnrichmentDoesNotCreateAuthority :
  ReviewEnrichmentAutomaticallyAuthority → ⊥
reviewEnrichmentDoesNotCreateAuthority ()

reviewEnrichmentDoesNotCreateCurrentLaw :
  ReviewEnrichmentAutomaticallyCurrentLaw → ⊥
reviewEnrichmentDoesNotCreateCurrentLaw ()
