module DASHI.Cognition.PNF.SensibLawReviewProjectionEconomyRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
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
