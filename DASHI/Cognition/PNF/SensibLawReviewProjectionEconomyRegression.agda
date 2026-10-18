module DASHI.Cognition.PNF.SensibLawReviewProjectionEconomyRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.String using (String)
open import Data.List.Base using ([]; _∷_)

import DASHI.Cognition.PNF.SensibLawReviewProjectionEconomyExact as Economy

fixtureInput : Economy.ReviewProjectionInputIdentity
fixtureInput =
  Economy.review-projection-input-identity
    "source-revision:fixture"
    "scale1:reconciliation-review-projection:v1"
    "sha256:fixture-review-input"
    "sha256:fixture-consumer-scope"

fixtureExactReviewProjectionReuse : Economy.ExactReviewProjectionReuse
fixtureExactReviewProjectionReuse =
  Economy.exact-review-projection-reuse
    fixtureInput
    ("review-item:a" ∷ "review-item:b" ∷ [])
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

fixtureReuseMatchesInput :
  Economy.ExactReviewProjectionReuse.exactInputIdentityMatched
    fixtureExactReviewProjectionReuse
  ≡ true
fixtureReuseMatchesInput = refl

fixtureReuseReopensPersistedProjection :
  Economy.ExactReviewProjectionReuse.persistedItemsReopened
    fixtureExactReviewProjectionReuse
  ≡ true
fixtureReuseReopensPersistedProjection = refl

fixtureReuseDoesNotRecomputeReviewCandidates :
  Economy.ExactReviewProjectionReuse.recomputesReviewCandidates
    fixtureExactReviewProjectionReuse
  ≡ false
fixtureReuseDoesNotRecomputeReviewCandidates = refl

fixtureReuseDoesNotCreateReviewDecision :
  Economy.ExactReviewProjectionReuse.createsReviewDecision
    fixtureExactReviewProjectionReuse
  ≡ false
fixtureReuseDoesNotCreateReviewDecision = refl

fixtureReuseDoesNotCreateTruth :
  Economy.ExactReviewProjectionReuse.createsClaimTruth
    fixtureExactReviewProjectionReuse
  ≡ false
fixtureReuseDoesNotCreateTruth = refl


fixtureUpstreamIdentityV2 : Economy.ReviewProjectionUpstreamIdentity
fixtureUpstreamIdentityV2 =
  Economy.review-projection-upstream-identity
    "source-revision:fixture"
    "parser-run:fixture"
    "scale1:persistent-pnf-fingerprint:v1"
    "scale1:reconciliation-review-projection:v1"
    "sha256:fixture-consumer-scope"
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

fixtureExactReviewProjectionReuseV2 :
  Economy.ExactReviewProjectionReuseV2
fixtureExactReviewProjectionReuseV2 =
  Economy.exact-review-projection-reuse-v2
    fixtureUpstreamIdentityV2
    ("review-item:a" ∷ "review-item:b" ∷ [])
    true refl
    true refl
    0 refl
    0 refl
    0 refl
    0 refl
    false refl
    false refl
    false refl
    false refl

fixtureV2ReuseScansNoPressureRows :
  Economy.ExactReviewProjectionReuseV2.pressureRowsScannedOnReuse
    fixtureExactReviewProjectionReuseV2
  ≡ 0
fixtureV2ReuseScansNoPressureRows = refl

fixtureV2ReuseScansNoContestationRows :
  Economy.ExactReviewProjectionReuseV2.contestationRowsScannedOnReuse
    fixtureExactReviewProjectionReuseV2
  ≡ 0
fixtureV2ReuseScansNoContestationRows = refl

fixtureV2ReuseScansNoOccurrenceRows :
  Economy.ExactReviewProjectionReuseV2.occurrenceRowsScannedOnReuse
    fixtureExactReviewProjectionReuseV2
  ≡ 0
fixtureV2ReuseScansNoOccurrenceRows = refl

fixtureV2ReusePerformsNoOccurrenceLookup :
  Economy.ExactReviewProjectionReuseV2.occurrenceLookupCountOnReuse
    fixtureExactReviewProjectionReuseV2
  ≡ 0
fixtureV2ReusePerformsNoOccurrenceLookup = refl

fixtureV2ReuseDoesNotCreateTruth :
  Economy.ExactReviewProjectionReuseV2.createsClaimTruthV2
    fixtureExactReviewProjectionReuseV2
  ≡ false
fixtureV2ReuseDoesNotCreateTruth = refl


fixtureDeltaReviewProjection : Economy.ReviewProjectionDeltaFibreReceipt
fixtureDeltaReviewProjection =
  Economy.review-projection-delta-fibre-receipt
    "source-revision:edited"
    "parser-run:edited"
    "scale1:persistent-pnf-fingerprint:v1"
    3
    3
    refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

fixtureDeltaReviewUsesExactChangedFibreSet :
  Economy.ReviewProjectionDeltaFibreReceipt.targetFibreCount
    fixtureDeltaReviewProjection
  ≡
  Economy.ReviewProjectionDeltaFibreReceipt.deltaFibreCount
    fixtureDeltaReviewProjection
fixtureDeltaReviewUsesExactChangedFibreSet = refl

fixtureDeltaReviewActuallyUsesDeltaInput :
  Economy.ReviewProjectionDeltaFibreReceipt.deltaInputUsed
    fixtureDeltaReviewProjection
  ≡ true
fixtureDeltaReviewActuallyUsesDeltaInput = refl

fixtureDeltaReviewDoesNotCreateAuthority :
  Economy.ReviewProjectionDeltaFibreReceipt.createsSemanticAuthorityDelta
    fixtureDeltaReviewProjection
  ≡ false
fixtureDeltaReviewDoesNotCreateAuthority = refl
