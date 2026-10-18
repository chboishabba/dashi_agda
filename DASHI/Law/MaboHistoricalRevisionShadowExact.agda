module DASHI.Law.MaboHistoricalRevisionShadowExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.MaboRevisionReopenExact as Reopen
import DASHI.Law.ClosedIsNotAdequateExact as Closed

------------------------------------------------------------------------
-- Controlled historical perturbation.
--
-- The shadow experiment uses two exact real source manifestations R0<R1, but
-- overlays R0 only in memory over the finite reviewed-current world.  It tests
-- whether a real source-manifestation change alters bounded context and/or the
-- consumer-visible identity frontier.  The fixture cannot itself create or
-- persist a review, identity, authority or adequacy result.
------------------------------------------------------------------------

data ShadowOutcome : Set where
  noHistoricalContextPerturbation : ShadowOutcome
  historicalContextChangedOnly : ShadowOutcome
  historicalConsumerFrontierChanged : ShadowOutcome

record HistoricalRevisionShadowReceipt : Set where
  constructor historicalRevisionShadowReceipt
  field
    exactHistoricalR0 : Bool
    exactHistoricalR0IsTrue : exactHistoricalR0 ≡ true

    exactReviewedR1 : Bool
    exactReviewedR1IsTrue : exactReviewedR1 ≡ true

    candidateSetsDiffer : Bool
    candidateSetsDifferIsTrue : candidateSetsDiffer ≡ true

    fixtureOnly : Bool
    fixtureOnlyIsTrue : fixtureOnly ≡ true

    persisted : Bool
    persistedIsFalse : persisted ≡ false

    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse :
      createsSemanticAuthority ≡ false

    createsClaimTruth : Bool
    createsClaimTruthIsFalse :
      createsClaimTruth ≡ false

    consumerAdequacyFormallyProved : Bool
    consumerAdequacyFormallyProvedIsFalse :
      consumerAdequacyFormallyProved ≡ false

open HistoricalRevisionShadowReceipt public

canonicalHistoricalRevisionShadowReceipt :
  HistoricalRevisionShadowReceipt
canonicalHistoricalRevisionShadowReceipt =
  historicalRevisionShadowReceipt
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

data ShadowFixtureAutomaticallyReviewed : Set where
data ShadowFixtureAutomaticallyAdequate : Set where
data ContextChangeAutomaticallyIdentityChange : Set where

shadowFixtureCannotReviewItself :
  ShadowFixtureAutomaticallyReviewed → ⊥
shadowFixtureCannotReviewItself ()

shadowFixtureCannotProveAdequacy :
  ShadowFixtureAutomaticallyAdequate → ⊥
shadowFixtureCannotProveAdequacy ()

contextChangeNeedNotChangeIdentityFrontier :
  ContextChangeAutomaticallyIdentityChange → ⊥
contextChangeNeedNotChangeIdentityFrontier ()

revisionReopenBoundary :
  Reopen.MaboRevisionReopenBoundary
revisionReopenBoundary =
  Reopen.canonicalMaboRevisionReopenBoundary

closedIsNotAdequateBoundary :
  Closed.ClosedIsNotAdequateBoundary
closedIsNotAdequateBoundary =
  Closed.canonicalClosedIsNotAdequateBoundary

record MaboHistoricalRevisionShadowBoundary : Set where
  constructor maboHistoricalRevisionShadowBoundary
  field
    historicalPerturbationUsesExactRevisionPair : Bool
    historicalPerturbationUsesExactRevisionPairIsTrue :
      historicalPerturbationUsesExactRevisionPair ≡ true

    historicalShadowMayPersistReview : Bool
    historicalShadowMayPersistReviewIsFalse :
      historicalShadowMayPersistReview ≡ false

    historicalContextDeltaMayTriggerRecomputation : Bool
    historicalContextDeltaMayTriggerRecomputationIsTrue :
      historicalContextDeltaMayTriggerRecomputation ≡ true

    historicalContextDeltaGuaranteesIdentityDelta : Bool
    historicalContextDeltaGuaranteesIdentityDeltaIsFalse :
      historicalContextDeltaGuaranteesIdentityDelta ≡ false

    unchangedConsumerFrontierProvesAdequacy : Bool
    unchangedConsumerFrontierProvesAdequacyIsFalse :
      unchangedConsumerFrontierProvesAdequacy ≡ false

open MaboHistoricalRevisionShadowBoundary public

canonicalMaboHistoricalRevisionShadowBoundary :
  MaboHistoricalRevisionShadowBoundary
canonicalMaboHistoricalRevisionShadowBoundary =
  maboHistoricalRevisionShadowBoundary
    true refl
    false refl
    true refl
    false refl
    false refl
