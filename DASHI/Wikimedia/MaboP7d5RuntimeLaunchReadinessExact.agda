module DASHI.Wikimedia.MaboP7d5RuntimeLaunchReadinessExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.MaboP7d5SlrRuntimeReceiptExact as Runtime
import DASHI.Wikimedia.MaboResidualDrivenWorldRunnerExact as Runner
import DASHI.Wikimedia.MaboReviewedEvidencePaymentExact as Reviewed
import DASHI.Wikimedia.MaboLiveIdentityLineageInteropExact as Lineage

------------------------------------------------------------------------
-- P7d.5 NATIVE-RUNTIME LAUNCH READINESS
--
-- This owner answers only the production-control question:
--   are the native SLR prerequisites now paid strongly enough to launch the
--   recurrent >=100 reviewed-identity-class campaign?
--
-- It does not claim the campaign has run, that the target has been reached,
-- that JMD parity has been observed, or that the Agda source has kernel GREEN.
------------------------------------------------------------------------

record P7d5RuntimeLaunchReadiness : Set where
  constructor p7d5-runtime-launch-readiness
  field
    nativeIdentityClassRuntimePaid : Bool
    nativeWorldObservationRuntimePaid : Bool
    nativeRevisionDigestRuntimePaid : Bool
    nativeReviewedEvidencePaymentPresent : Bool
    nativeIdentityLineagePgPaid : Bool
    recurrentRunnerGoldenBoundaryPresent : Bool
    nativeRunnerLaunchPrerequisitesPaid : Bool
    jmdGetterParityRequiredForNativeLaunch : Bool
    agdaKernelGreenRequiredToRunSlrCampaign : Bool
    recurrentHundredClassCampaignObserved : Bool
    hundredReviewedIdentityClassesReached : Bool
    launchReadinessCreatesSemanticAuthority : Bool
    launchReadinessCreatesClaimTruth : Bool
    launchReadinessCreatesAgdaProof : Bool

open P7d5RuntimeLaunchReadiness public

canonicalLaunchReadiness : P7d5RuntimeLaunchReadiness
canonicalLaunchReadiness =
  p7d5-runtime-launch-readiness
    (Runtime.worldIdentityClassRuntimeCertified Runtime.slrP7d5Payment)
    (Runtime.normalizedObservationRuntimeCertified Runtime.slrP7d5Payment)
    (Runtime.producerRevisionDigestRuntimeCertified Runtime.slrP7d5Payment)
    (Reviewed.reviewEmitted Reviewed.maboParticipantIdentityPayment)
    (Runtime.identityClassPgLineageObserved Runtime.slrP7d5Payment)
    (Runner.targetCountsReviewedIdentityClasses Runner.canonicalRecurrentRunnerBoundary)
    (Runner.launchPrerequisitesPaid Runner.nativeSlrCampaignLaunchPayment)
    false
    false
    (Runner.recurrentCampaignExecuted Runner.nativeSlrCampaignLaunchPayment)
    (Runner.hundredReviewedIdentityClassesObserved Runner.nativeSlrCampaignLaunchPayment)
    false
    false
    false

nativeRunnerLaunchPaid :
  nativeRunnerLaunchPrerequisitesPaid canonicalLaunchReadiness ≡ true
nativeRunnerLaunchPaid = refl

reviewPaymentPresent :
  nativeReviewedEvidencePaymentPresent canonicalLaunchReadiness ≡ true
reviewPaymentPresent = refl

campaignStillUnobserved :
  recurrentHundredClassCampaignObserved canonicalLaunchReadiness ≡ false
campaignStillUnobserved = refl

targetStillUnreachedByReceipt :
  hundredReviewedIdentityClassesReached canonicalLaunchReadiness ≡ false
targetStillUnreachedByReceipt = refl

------------------------------------------------------------------------
-- Canonical owner pins: readiness depends on distinct acquisition, review,
-- durable-lineage and runner boundaries rather than reducing them to one Bool
-- producer in the implementation architecture.
------------------------------------------------------------------------

_ : Set
_ = Runtime.P7d5RuntimePayment

_ : Set
_ = Runner.RecurrentCampaignLaunchPayment

_ : Set
_ = Reviewed.ReviewedEvidencePaymentReceipt

_ : Set
_ = Lineage.LiveLineageIdentityAttachment

------------------------------------------------------------------------
-- Non-collapse firewalls.
------------------------------------------------------------------------

data LaunchReadyEqualsCampaignExecuted : Set where
data LaunchReadyEqualsTargetComplete : Set where
data LaunchReadyCreatesSemanticAuthority : Set where
data LaunchReadyCreatesClaimTruth : Set where
data SlrLaunchRequiresJmdParity : Set where
data SlrLaunchRequiresAgdaKernelGreen : Set where

launchReadyDoesNotEqualCampaignExecuted :
  LaunchReadyEqualsCampaignExecuted → ⊥
launchReadyDoesNotEqualCampaignExecuted ()

launchReadyDoesNotEqualTargetComplete :
  LaunchReadyEqualsTargetComplete → ⊥
launchReadyDoesNotEqualTargetComplete ()

launchReadyDoesNotCreateSemanticAuthority :
  LaunchReadyCreatesSemanticAuthority → ⊥
launchReadyDoesNotCreateSemanticAuthority ()

launchReadyDoesNotCreateClaimTruth :
  LaunchReadyCreatesClaimTruth → ⊥
launchReadyDoesNotCreateClaimTruth ()

slrLaunchDoesNotRequireJmdParity : SlrLaunchRequiresJmdParity → ⊥
slrLaunchDoesNotRequireJmdParity ()

slrLaunchDoesNotRequireAgdaKernelGreen : SlrLaunchRequiresAgdaKernelGreen → ⊥
slrLaunchDoesNotRequireAgdaKernelGreen ()
