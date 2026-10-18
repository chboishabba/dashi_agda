module DASHI.Law.MaboHistoricalRevisionShadowRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.MaboHistoricalRevisionShadowExact as Shadow

boundary : Shadow.MaboHistoricalRevisionShadowBoundary
boundary = Shadow.canonicalMaboHistoricalRevisionShadowBoundary

exactPair :
  Shadow.historicalPerturbationUsesExactRevisionPair boundary ≡ true
exactPair =
  Shadow.historicalPerturbationUsesExactRevisionPairIsTrue boundary

fixtureCannotPersist :
  Shadow.historicalShadowMayPersistReview boundary ≡ false
fixtureCannotPersist =
  Shadow.historicalShadowMayPersistReviewIsFalse boundary

contextMayRecompute :
  Shadow.historicalContextDeltaMayTriggerRecomputation boundary ≡ true
contextMayRecompute =
  Shadow.historicalContextDeltaMayTriggerRecomputationIsTrue boundary

contextDoesNotGuaranteeIdentity :
  Shadow.historicalContextDeltaGuaranteesIdentityDelta boundary ≡ false
contextDoesNotGuaranteeIdentity =
  Shadow.historicalContextDeltaGuaranteesIdentityDeltaIsFalse boundary

unchangedFrontierIsNotAdequacy :
  Shadow.unchangedConsumerFrontierProvesAdequacy boundary ≡ false
unchangedFrontierIsNotAdequacy =
  Shadow.unchangedConsumerFrontierProvesAdequacyIsFalse boundary
