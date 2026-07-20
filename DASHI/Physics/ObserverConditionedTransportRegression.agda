module DASHI.Physics.ObserverConditionedTransportRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.ObserverConditionedTransportBridge

------------------------------------------------------------------------
-- Compact import and fail-closed regression surface.

candidateBridgeRemainsTrue :
  candidateBridgeOnly canonicalObserverConditionedTransportGovernance ≡ true
candidateBridgeRemainsTrue =
  candidateBridgeOnlyIsTrue canonicalObserverConditionedTransportGovernance

quotientConstructionRemainsOpen :
  quotientConstructed canonicalObserverConditionedTransportGovernance ≡ false
quotientConstructionRemainsOpen =
  quotientConstructedIsFalse canonicalObserverConditionedTransportGovernance

singleCausticUniversalClaimRemainsRejected :
  singleCausticAlwaysSufficient canonicalObserverConditionedTransportGovernance ≡ false
singleCausticUniversalClaimRemainsRejected =
  singleCausticAlwaysSufficientIsFalse
    canonicalObserverConditionedTransportGovernance

fullSolverEquivalenceRemainsOpen :
  physicallyEquivalentToFullSolver canonicalObserverConditionedTransportGovernance ≡ false
fullSolverEquivalenceRemainsOpen =
  physicallyEquivalentToFullSolverIsFalse
    canonicalObserverConditionedTransportGovernance

rtxSpeedupRemainsUnproved :
  fasterThanRTXProved canonicalObserverConditionedTransportGovernance ≡ false
rtxSpeedupRemainsUnproved =
  fasterThanRTXProvedIsFalse canonicalObserverConditionedTransportGovernance

waveSolverSpeedupRemainsUnproved :
  fasterThanWaveSolverProved canonicalObserverConditionedTransportGovernance ≡ false
waveSolverSpeedupRemainsUnproved =
  fasterThanWaveSolverProvedIsFalse
    canonicalObserverConditionedTransportGovernance
