module DASHI.Wikimedia.MaboResidualDrivenWorldRunnerValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Wikimedia.MaboResidualDrivenWorldRunnerExact

validationTargetIs100 : targetIdentityClasses ≡ 100
validationTargetIs100 = targetIdentityClassesIs100

validationCountsIdentityClasses :
  targetCountsReviewedIdentityClasses canonicalRecurrentRunnerBoundary ≡ true
validationCountsIdentityClasses = refl

validationStagesCycle :
  cycleRunsAgainstStagedSession canonicalRecurrentRunnerBoundary ≡ true
validationStagesCycle = refl

validationSinkBeforeCommit :
  sinkAcceptanceRequiredBeforeCommit canonicalRecurrentRunnerBoundary ≡ true
validationSinkBeforeCommit = refl

validationRecomputesFrontier :
  successfulCycleRecomputesFrontier canonicalRecurrentRunnerBoundary ≡ true
validationRecomputesFrontier = refl

validationNoIdentityReviewManufacture :
  runnerMayManufactureIdentityReview canonicalRecurrentRunnerBoundary ≡ false
validationNoIdentityReviewManufacture = refl

validationNoWorldDiagnosisManufacture :
  runnerMayManufactureWorldDiagnosis canonicalRecurrentRunnerBoundary ≡ false
validationNoWorldDiagnosisManufacture = refl

validationNoAuthorityPromotion :
  runnerCreatesSemanticAuthority canonicalRecurrentRunnerBoundary ≡ false
validationNoAuthorityPromotion = refl

validationNoClaimTruthPromotion :
  runnerCreatesClaimTruth canonicalRecurrentRunnerBoundary ≡ false
validationNoClaimTruthPromotion = refl

validationPreparedCycleHasReviewedIdentity :
  reviewedIdentityResolutionPresent canonicalPreparedCampaignCycleBoundary ≡ true
validationPreparedCycleHasReviewedIdentity = refl

validationPreparedCycleHasWorldObservation :
  postAcquisitionWorldObservationPresent canonicalPreparedCampaignCycleBoundary ≡ true
validationPreparedCycleHasWorldObservation = refl

validationPreparedCycleHasLineageSink :
  durableLineageSinkPresent canonicalPreparedCampaignCycleBoundary ≡ true
validationPreparedCycleHasLineageSink = refl

------------------------------------------------------------------------
-- Live SLR #24 payment: launch-ready is not campaign-complete.
------------------------------------------------------------------------

validationNativeRuntimeCertified :
  nativeRuntimeCertified nativeSlrCampaignLaunchPayment ≡ true
validationNativeRuntimeCertified = refl

validationPinnedProviderObservationObserved :
  pinnedProviderObservationObserved nativeSlrCampaignLaunchPayment ≡ true
validationPinnedProviderObservationObserved = refl

validationExactRevisionDigestObserved :
  exactRevisionDigestObserved nativeSlrCampaignLaunchPayment ≡ true
validationExactRevisionDigestObserved = refl

validationReviewedEvidencePaymentPresent :
  explicitReviewedEvidencePaymentPresent nativeSlrCampaignLaunchPayment ≡ true
validationReviewedEvidencePaymentPresent = refl

validationIdentityClassLineageObserved :
  identityClassDurableLineageObserved nativeSlrCampaignLaunchPayment ≡ true
validationIdentityClassLineageObserved = refl

validationLaunchPrerequisitesPaid :
  launchPrerequisitesPaid nativeSlrCampaignLaunchPayment ≡ true
validationLaunchPrerequisitesPaid = refl

validationCampaignExecutionStillUnobserved :
  recurrentCampaignExecuted nativeSlrCampaignLaunchPayment ≡ false
validationCampaignExecutionStillUnobserved = refl

validationTargetCompletionStillUnobserved :
  targetCompletionObserved nativeSlrCampaignLaunchPayment ≡ false
validationTargetCompletionStillUnobserved = refl

validationHundredClassesStillUnobserved :
  hundredReviewedIdentityClassesObserved nativeSlrCampaignLaunchPayment ≡ false
validationHundredClassesStillUnobserved = refl

validationJmdParityNotLaunchDependency :
  jmdCrossBackendParityRequiredToLaunch nativeSlrCampaignLaunchPayment ≡ false
validationJmdParityNotLaunchDependency = refl

validationLaunchNoAuthorityPromotion :
  launchPaymentCreatesSemanticAuthority nativeSlrCampaignLaunchPayment ≡ false
validationLaunchNoAuthorityPromotion = refl

validationLaunchNoClaimTruthPromotion :
  launchPaymentCreatesClaimTruth nativeSlrCampaignLaunchPayment ≡ false
validationLaunchNoClaimTruthPromotion = refl

validationLaunchNoAgdaProofPromotion :
  launchPaymentCreatesAgdaProof nativeSlrCampaignLaunchPayment ≡ false
validationLaunchNoAgdaProofPromotion = refl
