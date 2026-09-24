module DASHI.Law.GenericReviewedAuthorityIdentityEnrichmentRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.GenericReviewedAuthorityIdentityEnrichmentExact as Identity

boundary : Identity.ReviewedAuthorityIdentityEnrichmentBoundary
boundary =
  Identity.canonicalReviewedAuthorityIdentityEnrichmentBoundary

reviewCanPayMissingDate :
  Identity.reviewMaySupplyMissingDecisionDate boundary ≡ true
reviewCanPayMissingDate =
  Identity.reviewMaySupplyMissingDecisionDateIsTrue boundary

reviewedDatePersists :
  Identity.reviewedDatePersistsIntoTraceNode boundary ≡ true
reviewedDatePersists =
  Identity.reviewedDatePersistsIntoTraceNodeIsTrue boundary

conflictingDateFailsClosed :
  Identity.reviewedDateMaySilentlyContradictSourceDate boundary ≡ false
conflictingDateFailsClosed =
  Identity.reviewedDateMaySilentlyContradictSourceDateIsFalse boundary

sourceReceiptStaysImmutable :
  Identity.sourceReceiptIsMutatedByReview boundary ≡ false
sourceReceiptStaysImmutable =
  Identity.sourceReceiptIsMutatedByReviewIsFalse boundary

reviewCreatesNoAuthority :
  Identity.reviewEnrichmentCreatesLegalAuthority boundary ≡ false
reviewCreatesNoAuthority =
  Identity.reviewEnrichmentCreatesLegalAuthorityIsFalse boundary

reviewCreatesNoCurrentLaw :
  Identity.reviewEnrichmentCreatesCurrentLawConclusion boundary ≡ false
reviewCreatesNoCurrentLaw =
  Identity.reviewEnrichmentCreatesCurrentLawConclusionIsFalse boundary
