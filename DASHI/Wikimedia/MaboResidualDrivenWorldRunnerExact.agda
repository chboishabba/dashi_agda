module DASHI.Wikimedia.MaboResidualDrivenWorldRunnerExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.MaboIdentityClassTargetExact as Target
import DASHI.Wikimedia.MaboResidualDrivenWorldSessionExact as Session
import DASHI.Wikimedia.MaboP7d5SlrRuntimeReceiptExact as Runtime
import DASHI.Wikimedia.MaboLiveIdentityLineageInteropExact as LiveLineage
import DASHI.Wikimedia.MaboReviewedEvidencePaymentExact as Reviewed

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
-- OBSERVED NATIVE-SLR LAUNCH PAYMENT
--
-- SLR PR #24 at efba015c... has now supplied the concrete runtime prerequisites
-- for launching the recurrent campaign: Cargo/clippy GREEN, a real pinned P710
-- provider observation with exact revision+digest, and live v2 PostgreSQL
-- identity-class lineage.  The existing reviewed-evidence owner separately pays
-- the participant same-object requirement.  This record deliberately does NOT
-- claim that the recurrent campaign itself has run or that the >=100 target is
-- complete.
------------------------------------------------------------------------

record RecurrentCampaignLaunchPayment : Set where
  constructor recurrent-campaign-launch-payment
  field
    runtimeReceiptReference : Runtime.SlrP7d5ExecutionReceipt
    liveP710ObservationReference : Runtime.LiveMaboP710ObservationReceipt
    reviewedEvidencePaymentReference : Reviewed.ReviewedEvidencePaymentReceipt
    liveMaboCaseIdentityLineageReference : Runtime.LiveDiscoveryIdentityLineageReceipt
    liveEddieMaboIdentityLineageReference : Runtime.LiveDiscoveryIdentityLineageReceipt
    nativeRuntimeCertified : Bool
    pinnedProviderObservationObserved : Bool
    exactRevisionDigestObserved : Bool
    explicitReviewedEvidencePaymentPresent : Bool
    identityClassDurableLineageObserved : Bool
    reviewedIdentityClassTargetSemanticsPresent : Bool
    stagedSessionBoundaryPresent : Bool
    launchPrerequisitesPaid : Bool
    recurrentCampaignExecuted : Bool
    targetCompletionObserved : Bool
    hundredReviewedIdentityClassesObserved : Bool
    jmdCrossBackendParityRequiredToLaunch : Bool
    launchPaymentCreatesSemanticAuthority : Bool
    launchPaymentCreatesClaimTruth : Bool
    launchPaymentCreatesAgdaProof : Bool

open RecurrentCampaignLaunchPayment public

nativeSlrCampaignLaunchPayment : RecurrentCampaignLaunchPayment
nativeSlrCampaignLaunchPayment =
  recurrent-campaign-launch-payment
    Runtime.slrP7d5Execution
    Runtime.liveMaboP710Observation
    Reviewed.maboParticipantIdentityPayment
    Runtime.liveMaboCaseLineage
    Runtime.liveEddieMaboLineage
    true
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
    false
    false
    false

launchPrerequisitesPaidTrue :
  launchPrerequisitesPaid nativeSlrCampaignLaunchPayment ≡ true
launchPrerequisitesPaidTrue = refl

campaignExecutionStillUnobserved :
  recurrentCampaignExecuted nativeSlrCampaignLaunchPayment ≡ false
campaignExecutionStillUnobserved = refl

targetCompletionStillUnobserved :
  targetCompletionObserved nativeSlrCampaignLaunchPayment ≡ false
targetCompletionStillUnobserved = refl

hundredClassesStillUnobserved :
  hundredReviewedIdentityClassesObserved nativeSlrCampaignLaunchPayment ≡ false
hundredClassesStillUnobserved = refl

jmdParityDoesNotBlockNativeLaunch :
  jmdCrossBackendParityRequiredToLaunch nativeSlrCampaignLaunchPayment ≡ false
jmdParityDoesNotBlockNativeLaunch = refl

------------------------------------------------------------------------
-- Exact live lineage same-coordinate pins.
--
-- The live persisted rows are already attached to golden identities by
-- MaboLiveIdentityLineageInteropExact. Reusing those equalities here prevents
-- the runner from inventing a second identity-class namespace.
------------------------------------------------------------------------

maboCaseRunnerIdentityClassRef : String
maboCaseRunnerIdentityClassRef =
  Runtime.identityClassRef Runtime.liveMaboCaseLineage

eddieMaboRunnerIdentityClassRef : String
eddieMaboRunnerIdentityClassRef =
  Runtime.identityClassRef Runtime.liveEddieMaboLineage

maboCaseRunnerIdentityUsesLiveGoldenWeld :
  maboCaseRunnerIdentityClassRef
  ≡ Runtime.identityClassRef Runtime.liveMaboCaseLineage
maboCaseRunnerIdentityUsesLiveGoldenWeld = refl

eddieMaboRunnerIdentityUsesLiveGoldenWeld :
  eddieMaboRunnerIdentityClassRef
  ≡ Runtime.identityClassRef Runtime.liveEddieMaboLineage
eddieMaboRunnerIdentityUsesLiveGoldenWeld = refl

_ : Set
_ = LiveLineage.LiveLineageIdentityAttachment

_ : Set
_ = Session.WorldExpansionSessionBoundary

_ : Set
_ = Reviewed.ReviewedEvidenceCoordinate

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
data LaunchPrerequisitesEqualCampaignExecution : Set where
data LaunchPrerequisitesEqualTargetCompletion : Set where
data NativeLaunchRequiresJmdParity : Set where
data RetrievedObservationEqualsReviewedEvidencePayment : Set where

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

launchPrerequisitesDoNotEqualCampaignExecution :
  LaunchPrerequisitesEqualCampaignExecution → ⊥
launchPrerequisitesDoNotEqualCampaignExecution ()

launchPrerequisitesDoNotEqualTargetCompletion :
  LaunchPrerequisitesEqualTargetCompletion → ⊥
launchPrerequisitesDoNotEqualTargetCompletion ()

nativeLaunchDoesNotRequireJmdParity : NativeLaunchRequiresJmdParity → ⊥
nativeLaunchDoesNotRequireJmdParity ()

retrievedObservationDoesNotEqualReviewedEvidencePayment :
  RetrievedObservationEqualsReviewedEvidencePayment → ⊥
retrievedObservationDoesNotEqualReviewedEvidencePayment ()
