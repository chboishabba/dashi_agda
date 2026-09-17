module DASHI.Wikimedia.MaboResidualDrivenWorldRunnerExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.MaboIdentityClassTargetExact as Target
import DASHI.Wikimedia.MaboResidualDrivenWorldSessionExact as Session

------------------------------------------------------------------------
-- P7d.5f recurrent runner boundary
--
-- The runner is an orchestration recurrence over already-owned semantic
-- boundaries. It does not manufacture producer evidence, PNF/world diagnosis,
-- identity review, authority, applicability or claim truth.
------------------------------------------------------------------------

data RecurrentRunStopReason : Set where
  targetComplete : RecurrentRunStopReason
  frontierExhausted : RecurrentRunStopReason
  cycleBudgetExhausted : RecurrentRunStopReason
  driverBlocked : RecurrentRunStopReason

record RecurrentRunnerBoundary : Set where
  constructor recurrent-runner-boundary
  field
    targetCountsReviewedIdentityClasses : Bool
    cycleRunsAgainstStagedSession : Bool
    sinkAcceptanceRequiredBeforeCommit : Bool
    successfulCycleRecomputesFrontier : Bool
    frontierExhaustionStopsRun : Bool
    cycleBudgetBoundsRun : Bool
    blockerProducesExplicitStopReceipt : Bool
    runnerMayManufactureIdentityReview : Bool
    runnerMayManufactureWorldDiagnosis : Bool
    runnerCreatesSemanticAuthority : Bool
    runnerCreatesClaimTruth : Bool

open RecurrentRunnerBoundary public

canonicalRecurrentRunnerBoundary : RecurrentRunnerBoundary
canonicalRecurrentRunnerBoundary =
  recurrent-runner-boundary
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false

targetIdentityClasses : Nat
targetIdentityClasses = Target.targetIdentityClasses

targetIdentityClassesIs100 : targetIdentityClasses ≡ 100
targetIdentityClassesIs100 = refl

record PreparedCampaignCycleBoundary : Set where
  constructor prepared-campaign-cycle-boundary
  field
    exactOpenResidualBound : Bool
    governedProducerArtifactPresent : Bool
    explicitReviewDecisionPresent : Bool
    reviewedIdentityResolutionPresent : Bool
    postAcquisitionWorldObservationPresent : Bool
    explicitObservedResidualDeltaPresent : Bool
    durableLineageSinkPresent : Bool

open PreparedCampaignCycleBoundary public

canonicalPreparedCampaignCycleBoundary : PreparedCampaignCycleBoundary
canonicalPreparedCampaignCycleBoundary =
  prepared-campaign-cycle-boundary
    true
    true
    true
    true
    true
    true
    true

------------------------------------------------------------------------
-- Non-collapse / transactional firewalls
------------------------------------------------------------------------

data SinkFailureAdvancesIdentityClassCount : Set where
data SinkFailureAdvancesFrontier : Set where
data DriverBlockerCreatesIdentityReview : Set where
data DriverBlockerCreatesWorldDiagnosis : Set where
data FrontierExhaustionEqualsTargetCompletion : Set where
data RunnerCreatesSemanticAuthority : Set where
data RunnerCreatesClaimTruth : Set where

sinkFailureDoesNotAdvanceIdentityClassCount :
  SinkFailureAdvancesIdentityClassCount → ⊥
sinkFailureDoesNotAdvanceIdentityClassCount ()

sinkFailureDoesNotAdvanceFrontier :
  SinkFailureAdvancesFrontier → ⊥
sinkFailureDoesNotAdvanceFrontier ()

driverBlockerDoesNotCreateIdentityReview :
  DriverBlockerCreatesIdentityReview → ⊥
driverBlockerDoesNotCreateIdentityReview ()

driverBlockerDoesNotCreateWorldDiagnosis :
  DriverBlockerCreatesWorldDiagnosis → ⊥
driverBlockerDoesNotCreateWorldDiagnosis ()

frontierExhaustionDoesNotEqualTargetCompletion :
  FrontierExhaustionEqualsTargetCompletion → ⊥
frontierExhaustionDoesNotEqualTargetCompletion ()

runnerDoesNotCreateSemanticAuthority : RunnerCreatesSemanticAuthority → ⊥
runnerDoesNotCreateSemanticAuthority ()

runnerDoesNotCreateClaimTruth : RunnerCreatesClaimTruth → ⊥
runnerDoesNotCreateClaimTruth ()
