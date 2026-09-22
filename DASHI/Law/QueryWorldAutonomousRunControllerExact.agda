module DASHI.Law.QueryWorldAutonomousRunControllerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.QueryScopedWorldCoordinateImpactExact as Impact
import DASHI.Law.QueryWorldCoverageInvalidationExact as Coverage
import DASHI.Law.QueryWorldFormalWitnessStalenessExact as Witness
import DASHI.Law.ClosedIsNotAdequateExact as Closed

------------------------------------------------------------------------
-- S15 × S18 autonomous query-world run controller.
--
-- The controller owns only the semantic decision:
--
--   world change + Q
--     -> preserve operational closure by proved invariance
--      | reopen exact research
--      | require fresh adequacy witness
--      | theorem-backed ConsumerAdequate
--      | explicit unresolved / budget stop
--
-- It does not acquire sources, perform reviews, or create legal truth.
------------------------------------------------------------------------

data RunDecision : Set where
  preserveOperationalClosureByInvariance : RunDecision
  reopenExactResearch : RunDecision
  requireFreshAdequacyWitness : RunDecision
  consumerAdequate : RunDecision
  explicitlyUnresolved : RunDecision
  budgetExhausted : RunDecision

data WorldImpact : Set where
  noWorldCoordinateChange : WorldImpact
  consumerInvariantChange : WorldImpact
  consumerRelevantChange : WorldImpact

data AdequacyState : Set where
  noFormalWitness : AdequacyState
  currentFactorsThroughWitness : AdequacyState
  exactNonfactorabilityWitness : AdequacyState

decide :
  WorldImpact →
  AdequacyState →
  RunDecision
decide noWorldCoordinateChange noFormalWitness =
  requireFreshAdequacyWitness
decide noWorldCoordinateChange currentFactorsThroughWitness =
  consumerAdequate
decide noWorldCoordinateChange exactNonfactorabilityWitness =
  reopenExactResearch
decide consumerInvariantChange noFormalWitness =
  preserveOperationalClosureByInvariance
decide consumerInvariantChange currentFactorsThroughWitness =
  consumerAdequate
decide consumerInvariantChange exactNonfactorabilityWitness =
  reopenExactResearch
decide consumerRelevantChange noFormalWitness =
  reopenExactResearch
decide consumerRelevantChange currentFactorsThroughWitness =
  consumerAdequate
decide consumerRelevantChange exactNonfactorabilityWitness =
  reopenExactResearch

irrelevantChangePreservesOnlyOperationalClosure :
  decide consumerInvariantChange noFormalWitness
  ≡
  preserveOperationalClosureByInvariance
irrelevantChangePreservesOnlyOperationalClosure = refl

sameWorldWithoutWitnessStillNeedsProof :
  decide noWorldCoordinateChange noFormalWitness
  ≡
  requireFreshAdequacyWitness
sameWorldWithoutWitnessStillNeedsProof = refl

relevantChangeWithoutFreshWitnessReopens :
  decide consumerRelevantChange noFormalWitness
  ≡
  reopenExactResearch
relevantChangeWithoutFreshWitnessReopens = refl

freshFactorsThroughMayCertifyCurrentWorld :
  decide consumerRelevantChange currentFactorsThroughWitness
  ≡
  consumerAdequate
freshFactorsThroughMayCertifyCurrentWorld = refl

data InvariantClosureAutomaticallyAdequate : Set where
data RelevantChangeMayPreserveOldClosure : Set where
data StaleWitnessMayCertifyCurrentWorld : Set where

invariancePreservesClosureNotAdequacy :
  InvariantClosureAutomaticallyAdequate → ⊥
invariancePreservesClosureNotAdequacy ()

consumerRelevantChangeCannotPreserveOldClosure :
  RelevantChangeMayPreserveOldClosure → ⊥
consumerRelevantChangeCannotPreserveOldClosure ()

staleWitnessCannotCertifyCurrentWorld :
  StaleWitnessMayCertifyCurrentWorld → ⊥
staleWitnessCannotCertifyCurrentWorld ()

impactBoundary :
  Impact.QueryScopedWorldCoordinateImpactBoundary
impactBoundary =
  Impact.canonicalQueryScopedWorldCoordinateImpactBoundary

coverageBoundary :
  Coverage.QueryWorldCoverageInvalidationBoundary
coverageBoundary =
  Coverage.canonicalQueryWorldCoverageInvalidationBoundary

witnessBoundary :
  Witness.QueryWorldFormalWitnessStalenessBoundary
witnessBoundary =
  Witness.canonicalQueryWorldFormalWitnessStalenessBoundary

closedBoundary :
  Closed.ClosedIsNotAdequateBoundary
closedBoundary =
  Closed.canonicalClosedIsNotAdequateBoundary

record QueryWorldAutonomousRunControllerBoundary : Set where
  constructor queryWorldAutonomousRunControllerBoundary
  field
    consumerInvariantChangeMayPreserveOperationalClosure : Bool
    consumerInvariantChangeMayPreserveOperationalClosureIsTrue :
      consumerInvariantChangeMayPreserveOperationalClosure ≡ true

    preservedOperationalClosureIsConsumerAdequacyProof : Bool
    preservedOperationalClosureIsConsumerAdequacyProofIsFalse :
      preservedOperationalClosureIsConsumerAdequacyProof ≡ false

    consumerRelevantChangeMayPreserveOldClosureWithoutProof : Bool
    consumerRelevantChangeMayPreserveOldClosureWithoutProofIsFalse :
      consumerRelevantChangeMayPreserveOldClosureWithoutProof ≡ false

    consumerRelevantChangeMayReopenExactResearch : Bool
    consumerRelevantChangeMayReopenExactResearchIsTrue :
      consumerRelevantChangeMayReopenExactResearch ≡ true

    freshFactorsThroughWitnessMayCertifyCurrentWorld : Bool
    freshFactorsThroughWitnessMayCertifyCurrentWorldIsTrue :
      freshFactorsThroughWitnessMayCertifyCurrentWorld ≡ true

    stalePositiveWitnessMayCertifyCurrentWorld : Bool
    stalePositiveWitnessMayCertifyCurrentWorldIsFalse :
      stalePositiveWitnessMayCertifyCurrentWorld ≡ false

    staleNegativeWitnessMayReopenCurrentWorld : Bool
    staleNegativeWitnessMayReopenCurrentWorldIsFalse :
      staleNegativeWitnessMayReopenCurrentWorld ≡ false

    runMayStopMeansOperationalFrontierClosed : Bool
    runMayStopMeansOperationalFrontierClosedIsFalse :
      runMayStopMeansOperationalFrontierClosed ≡ false

    operationalFrontierClosedMeansConsumerAdequate : Bool
    operationalFrontierClosedMeansConsumerAdequateIsFalse :
      operationalFrontierClosedMeansConsumerAdequate ≡ false

    controllerCreatesSemanticAuthority : Bool
    controllerCreatesSemanticAuthorityIsFalse :
      controllerCreatesSemanticAuthority ≡ false

    controllerCreatesClaimTruth : Bool
    controllerCreatesClaimTruthIsFalse :
      controllerCreatesClaimTruth ≡ false

open QueryWorldAutonomousRunControllerBoundary public

canonicalQueryWorldAutonomousRunControllerBoundary :
  QueryWorldAutonomousRunControllerBoundary
canonicalQueryWorldAutonomousRunControllerBoundary =
  queryWorldAutonomousRunControllerBoundary
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
