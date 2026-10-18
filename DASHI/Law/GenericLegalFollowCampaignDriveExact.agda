module DASHI.Law.GenericLegalFollowCampaignDriveExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Deterministic campaign driving.
--
-- The driver may execute already-admitted deterministic transport/plumbing.
-- It must stop at explicit legal review gates.  Driving is therefore not
-- review automation and cannot itself create authority or current-law truth.
------------------------------------------------------------------------

data CampaignGate : Set where
  outboundCitationAcquisition : CampaignGate
  authorityIdentityReview : CampaignGate
  authorityTreatmentReview : CampaignGate
  contextExpansion : CampaignGate
  temporalAlternative : CampaignGate
  budgetExhausted : CampaignGate
  complete : CampaignGate

data DriveDisposition : Set where
  executeDeterministicAcquisition : DriveDisposition
  awaitIdentityReview : DriveDisposition
  awaitTreatmentReview : DriveDisposition
  awaitExplicitOperator : DriveDisposition
  stopBudget : DriveDisposition
  stopComplete : DriveDisposition

drive : CampaignGate → DriveDisposition
drive outboundCitationAcquisition = executeDeterministicAcquisition
drive authorityIdentityReview = awaitIdentityReview
drive authorityTreatmentReview = awaitTreatmentReview
drive contextExpansion = awaitExplicitOperator
drive temporalAlternative = awaitExplicitOperator
drive budgetExhausted = stopBudget
drive complete = stopComplete

identityReviewStopsDriver :
  drive authorityIdentityReview ≡ awaitIdentityReview
identityReviewStopsDriver = refl

treatmentReviewStopsDriver :
  drive authorityTreatmentReview ≡ awaitTreatmentReview
treatmentReviewStopsDriver = refl

record GenericLegalFollowCampaignDriveBoundary : Set where
  constructor genericLegalFollowCampaignDriveBoundary
  field
    deterministicAcquisitionMayBeDriven : Bool
    deterministicAcquisitionMayBeDrivenIsTrue :
      deterministicAcquisitionMayBeDriven ≡ true

    identityReviewMayBeBypassedByDriver : Bool
    identityReviewMayBeBypassedByDriverIsFalse :
      identityReviewMayBeBypassedByDriver ≡ false

    treatmentReviewMayBeBypassedByDriver : Bool
    treatmentReviewMayBeBypassedByDriverIsFalse :
      treatmentReviewMayBeBypassedByDriver ≡ false

    terminalGateMayInventFurtherWork : Bool
    terminalGateMayInventFurtherWorkIsFalse :
      terminalGateMayInventFurtherWork ≡ false

    driverCreatesLegalAuthority : Bool
    driverCreatesLegalAuthorityIsFalse :
      driverCreatesLegalAuthority ≡ false

    driverCreatesCurrentLawConclusion : Bool
    driverCreatesCurrentLawConclusionIsFalse :
      driverCreatesCurrentLawConclusion ≡ false

open GenericLegalFollowCampaignDriveBoundary public

canonicalGenericLegalFollowCampaignDriveBoundary :
  GenericLegalFollowCampaignDriveBoundary
canonicalGenericLegalFollowCampaignDriveBoundary =
  genericLegalFollowCampaignDriveBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

data DriverMayBypassIdentityReview : Set where
data DriverMayBypassTreatmentReview : Set where
data DriverAutomaticallyCreatesAuthority : Set where

driverCannotBypassIdentityReview :
  DriverMayBypassIdentityReview → ⊥
driverCannotBypassIdentityReview ()

driverCannotBypassTreatmentReview :
  DriverMayBypassTreatmentReview → ⊥
driverCannotBypassTreatmentReview ()

driverDoesNotCreateAuthority :
  DriverAutomaticallyCreatesAuthority → ⊥
driverDoesNotCreateAuthority ()
