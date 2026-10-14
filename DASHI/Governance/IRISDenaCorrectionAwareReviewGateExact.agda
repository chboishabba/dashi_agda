module DASHI.Governance.IRISDenaCorrectionAwareReviewGateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Governance.IRISDenaHansardCorrectionAwareEvidenceExact as Hansard
import DASHI.Law.SensibLawRealMatterReviewDecisionExact as Review

------------------------------------------------------------------------
-- IRIS DENA / CORRECTION-AWARE EXACT REVIEW GATE
--
-- The current source owner already proves that the relevant primary object is
-- not merely transcript 29619, but transcript 29619 plus any applicable later
-- Chief-of-Navy correction.  This owner cross-pollinates the generic exact
-- human-review machinery already present on master.
--
-- Acquisition, review, source authority and proposition truth remain separate:
--   bytes acquired != reviewed
--   reviewed != accepted proposition
--   review receipt != source authority
--   review receipt != historical truth
------------------------------------------------------------------------

record CorrectionAwareReviewDemand : Set where
  constructor correction-aware-review-demand
  field
    sourceBundle : Hansard.CorrectionAwarePrimaryBundle
    transcriptManifestationRef : String
    correctionManifestationRef : String
    propositionRef : String
    consumerRef : String
    transcriptContentAcquired : Bool
    transcriptContentAcquiredIsFalse : transcriptContentAcquired ≡ false
    correctionContentAcquired : Bool
    correctionContentAcquiredIsFalse : correctionContentAcquired ≡ false
    applicableCorrectionResolved : Bool
    applicableCorrectionResolvedIsFalse : applicableCorrectionResolved ≡ false
    exactReviewBindingPaid : Bool
    exactReviewBindingPaidIsFalse : exactReviewBindingPaid ≡ false
    dutyClassPromotionPaid : Bool
    dutyClassPromotionPaidIsFalse : dutyClassPromotionPaid ≡ false

open CorrectionAwareReviewDemand public

canonicalReviewDemand : CorrectionAwareReviewDemand
canonicalReviewDemand =
  correction-aware-review-demand
    Hansard.canonicalPrimaryBundle
    "FADT-2026-06-03-transcript-29619-pp49-52"
    "Chief-of-Navy-correction-applicable-to-29619-pp49-52"
    "what duty classes were attributed to the three embedded Australian submariners during the IRIS Dena engagement"
    "IRIS-Dena duty-class consumer"
    false refl
    false refl
    false refl
    false refl
    false refl

record ReviewedCorrectionAwarePrimaryBundle : Set where
  constructor reviewed-correction-aware-primary-bundle
  field
    genericReview : Review.GenericHumanReviewReceipt
    exactBinding : Review.ExactReviewItemBinding
    transcriptManifestationRef : String
    correctionManifestationRef : String
    propositionRef : String
    consumerRef : String
    correctionApplicabilityResolved : Bool
    correctionApplicabilityResolvedIsTrue :
      correctionApplicabilityResolved ≡ true
    transcriptAndCorrectionReviewedTogether : Bool
    transcriptAndCorrectionReviewedTogetherIsTrue :
      transcriptAndCorrectionReviewedTogether ≡ true
    createsSourceAuthority : Bool
    createsSourceAuthorityIsFalse : createsSourceAuthority ≡ false
    createsHistoricalTruth : Bool
    createsHistoricalTruthIsFalse : createsHistoricalTruth ≡ false
    exactDutyClosed : Bool
    exactDutyClosedIsFalse : exactDutyClosed ≡ false

open ReviewedCorrectionAwarePrimaryBundle public

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data TranscriptAcquiredMeansReviewed : Set where
data TranscriptReviewedWithoutCorrectionIsCorrectionAware : Set where
data GenericReviewReceiptCreatesPrimaryAuthority : Set where
data ExactReviewBindingCreatesHistoricalTruth : Set where
data DutyClassReviewDeterminesExactWatchTask : Set where

acquiredDoesNotMeanReviewed : TranscriptAcquiredMeansReviewed → ⊥
acquiredDoesNotMeanReviewed ()

transcriptAloneIsNotCorrectionAwareReview :
  TranscriptReviewedWithoutCorrectionIsCorrectionAware → ⊥
transcriptAloneIsNotCorrectionAwareReview ()

genericReviewDoesNotCreatePrimaryAuthority :
  GenericReviewReceiptCreatesPrimaryAuthority → ⊥
genericReviewDoesNotCreatePrimaryAuthority ()

exactReviewDoesNotCreateHistoricalTruth :
  ExactReviewBindingCreatesHistoricalTruth → ⊥
exactReviewDoesNotCreateHistoricalTruth ()

dutyClassReviewDoesNotDetermineExactTask :
  DutyClassReviewDeterminesExactWatchTask → ⊥
dutyClassReviewDoesNotDetermineExactTask ()

reviewBoundary : Review.RealMatterReviewBoundary
reviewBoundary = Review.canonicalRealMatterReviewBoundary
