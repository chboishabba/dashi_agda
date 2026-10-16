module DASHI.Biology.BCICalibrationAgencyBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.NeuralPredictionDirectionExact as Prediction
import DASHI.Biology.AliceBrownThreadInquirySynthesisExact as Alice

------------------------------------------------------------------------
-- BCI CALIBRATION BURDEN / CAPABILITY BRIDGE
--
-- Reduced calibration burden can widen practical reachability/access, but a
-- company-reported decoder-efficiency change is not promoted to participant
-- autonomy, satisfaction, quality of life, clinical efficacy or preference.
-- Alice Brown's capability/voice boundary is reused as a methodological owner:
-- access/support != agency, and adult/external observation != participant
-- experience.
------------------------------------------------------------------------

data ParticipationBurdenCoordinate : Set where
  calibrationTimeBurden : ParticipationBurdenCoordinate
  setupAndMaintenanceBurden : ParticipationBurdenCoordinate
  cognitiveTaskBurden : ParticipationBurdenCoordinate
  failureRecoveryBurden : ParticipationBurdenCoordinate
  reportingAndStudyBurden : ParticipationBurdenCoordinate

data ParticipantOutcomeCoordinate : Set where
  participantReportedAgency : ParticipantOutcomeCoordinate
  participantReportedSatisfaction : ParticipantOutcomeCoordinate
  functionalIndependence : ParticipantOutcomeCoordinate
  clinicalBenefit : ParticipantOutcomeCoordinate
  qualityOfLife : ParticipantOutcomeCoordinate

record BCICalibrationAgencyBridge : Set where
  constructor bci-calibration-agency-bridge
  field
    provenance : Prediction.NeuralinkProvenanceSplit
    aliceSynthesis : Alice.AliceBrownThreadInquirySynthesis
    calibrationBurden : ParticipationBurdenCoordinate
    externalPerformanceReference : String
    participantExperienceReference : String
    reducedBurdenMayExpandReachability : Bool
    reducedBurdenMayExpandReachabilityIsTrue :
      reducedBurdenMayExpandReachability ≡ true
    reducedBurdenEqualsAgency : Bool
    reducedBurdenEqualsAgencyIsFalse : reducedBurdenEqualsAgency ≡ false
    companyPerformanceMetricEqualsParticipantExperience : Bool
    companyPerformanceMetricEqualsParticipantExperienceIsFalse :
      companyPerformanceMetricEqualsParticipantExperience ≡ false
    participantVoiceRequiredForParticipantExperienceClaim : Bool
    participantVoiceRequiredForParticipantExperienceClaimIsTrue :
      participantVoiceRequiredForParticipantExperienceClaim ≡ true

open BCICalibrationAgencyBridge public

canonicalBCICalibrationAgencyBridge : BCICalibrationAgencyBridge
canonicalBCICalibrationAgencyBridge =
  bci-calibration-agency-bridge
    Prediction.canonicalNeuralinkProvenanceSplit
    Alice.canonicalAliceBrownThreadInquirySynthesis
    calibrationTimeBurden
    "decoder calibration frequency/time, longitudinal decoder stability and task throughput"
    "participant-reported burden, preference, satisfaction, experienced autonomy and situated use context remain separate evidence coordinates"
    true refl false refl false refl true refl

data ReducedCalibrationCreatesAgencyPermission : Set where
data ExternalMetricCreatesParticipantExperiencePermission : Set where

reducedCalibrationDoesNotDefinitionallyCreateAgency :
  ReducedCalibrationCreatesAgencyPermission → Alice.Never
reducedCalibrationDoesNotDefinitionallyCreateAgency ()

externalMetricDoesNotCreateParticipantExperience :
  ExternalMetricCreatesParticipantExperiencePermission → Alice.Never
externalMetricDoesNotCreateParticipantExperience ()

record BCICalibrationAgencyBoundary : Set where
  constructor bci-calibration-agency-boundary
  field
    calibrationBurdenRepresented : Bool
    calibrationBurdenRepresentedIsTrue : calibrationBurdenRepresented ≡ true
    capabilityExpansionReadingAvailable : Bool
    capabilityExpansionReadingAvailableIsTrue :
      capabilityExpansionReadingAvailable ≡ true
    accessAutomaticallyEqualsAgency : Bool
    accessAutomaticallyEqualsAgencyIsFalse : accessAutomaticallyEqualsAgency ≡ false
    performanceAutomaticallyEqualsExperience : Bool
    performanceAutomaticallyEqualsExperienceIsFalse :
      performanceAutomaticallyEqualsExperience ≡ false
    clinicalBenefitAutomaticallyEstablished : Bool
    clinicalBenefitAutomaticallyEstablishedIsFalse :
      clinicalBenefitAutomaticallyEstablished ≡ false
    participantVoiceRemainsIndependentEvidence : Bool
    participantVoiceRemainsIndependentEvidenceIsTrue :
      participantVoiceRemainsIndependentEvidence ≡ true

canonicalBCICalibrationAgencyBoundary : BCICalibrationAgencyBoundary
canonicalBCICalibrationAgencyBoundary =
  bci-calibration-agency-boundary
    true refl true refl false refl false refl false refl true refl
