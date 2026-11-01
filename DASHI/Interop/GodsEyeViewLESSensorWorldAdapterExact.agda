module DASHI.Interop.GodsEyeViewLESSensorWorldAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.GodsEyeViewRuntimeNeutralAcquisitionABIExact as ABI
import DASHI.Interop.GodsEyeViewAcquisitionResultAssessmentBridgeExact as Assessment

------------------------------------------------------------------------
-- LES / REMOTE OR FIELD SENSOR ACQUISITION -> WORLD ACQUISITION ABI
--
-- A sensor result may refine an ecological observation while leaving mechanism,
-- calibration, management history, local knowledge, Country/community authority
-- and intervention authority unresolved.  This adapter therefore transports
-- evidence only; the generic assessment loop decides whether the live residual
-- is paid, remains open, splits, or is reactivated.
------------------------------------------------------------------------

record BoundLESSensorWorldRequest
    (request : ABI.RuntimeNeutralAcquisitionRequest) : Set where
  constructor bound-les-sensor-world-request
  field
    providerIsSensorObservation :
      ABI.providerKind request ≡ ABI.sensorObservationProvider
    requestedCarrierIsCalibratedSensor :
      ABI.requestedCarrier request ≡ ABI.calibratedSensorCarrier

    farmCountryOrSiteReference : String
    observationCoordinateReference : String
    sensorOrInstrumentReference : String
    boundedSpatialFootprintReference : String
    boundedTemporalWindowReference : String
    historicalBaselineReference : String
    calibrationReference : String
    uncertaintyBudgetReference : String
    localKnowledgeReference : String
    countryOrCommunityAuthorityReference : String
    interventionAuthorityReference : String
    mechanismDiscriminatorReference : String
    bindingReference : String

open BoundLESSensorWorldRequest public

data LESSensorAcquisitionOutcome : Set where
  executedWithCalibratedObservation : LESSensorAcquisitionOutcome
  executedNoSensorMatch : LESSensorAcquisitionOutcome
  sensorAcquisitionBlocked : LESSensorAcquisitionOutcome
  sensorProviderUnavailable : LESSensorAcquisitionOutcome
  sensorAcquisitionFailed : LESSensorAcquisitionOutcome

executionStatusFor : LESSensorAcquisitionOutcome → ABI.AcquisitionExecutionStatus
executionStatusFor executedWithCalibratedObservation = ABI.executedWithOutput
executionStatusFor executedNoSensorMatch = ABI.executedNoMatch
executionStatusFor sensorAcquisitionBlocked = ABI.blockedBeforeExecution
executionStatusFor sensorProviderUnavailable = ABI.providerUnavailable
executionStatusFor sensorAcquisitionFailed = ABI.executionFailed

sensorOutcomeAllowsSemanticAssessment : LESSensorAcquisitionOutcome → Bool
sensorOutcomeAllowsSemanticAssessment executedWithCalibratedObservation = true
sensorOutcomeAllowsSemanticAssessment executedNoSensorMatch = false
sensorOutcomeAllowsSemanticAssessment sensorAcquisitionBlocked = false
sensorOutcomeAllowsSemanticAssessment sensorProviderUnavailable = false
sensorOutcomeAllowsSemanticAssessment sensorAcquisitionFailed = false

genericAssessmentAdmissionAgrees :
  (outcome : LESSensorAcquisitionOutcome) →
  Assessment.executionAllowsSemanticAssessment (executionStatusFor outcome)
  ≡ sensorOutcomeAllowsSemanticAssessment outcome
genericAssessmentAdmissionAgrees executedWithCalibratedObservation = refl
genericAssessmentAdmissionAgrees executedNoSensorMatch = refl
genericAssessmentAdmissionAgrees sensorAcquisitionBlocked = refl
genericAssessmentAdmissionAgrees sensorProviderUnavailable = refl
genericAssessmentAdmissionAgrees sensorAcquisitionFailed = refl

record LESSensorWorldAcquisitionReceipt
    {request : ABI.RuntimeNeutralAcquisitionRequest}
    (bound : BoundLESSensorWorldRequest request) : Set₁ where
  constructor les-sensor-world-acquisition-receipt
  field
    outcome : LESSensorAcquisitionOutcome
    providerExecutionReference : String
    observationTimeReference : String
    exactSpatialOrInstrumentCoordinateReference : String
    contentIdentityOrHashReference : String
    coverageReference : String
    uncertaintyReference : String
    provenanceReference : String
    acquisitionAuthorityReference : String
    rawEvidenceReference : String
    providerInterpretationReference : String
    resultIdentityReference : String

    calibrationAssessmentReference : String
    baselineAssessmentReference : String
    mechanismAlternativeReference : String
    localKnowledgeAssessmentReference : String
    countryAuthorityAssessmentReference : String
    interventionAuthorityAssessmentReference : String
    validationReference : String

open LESSensorWorldAcquisitionReceipt public

sensorReceiptToRuntimeResult :
  ∀ {request}
    {bound : BoundLESSensorWorldRequest request} →
  LESSensorWorldAcquisitionReceipt bound →
  ABI.RuntimeNeutralAcquisitionResult request
sensorReceiptToRuntimeResult {bound = bound} receipt =
  ABI.runtime-neutral-acquisition-result
    (executionStatusFor (outcome receipt))
    (providerExecutionReference receipt)
    ABI.calibratedSensorCarrier
    "LES sensor adapter returns the calibrated-sensor carrier required by the bound request"
    (sensorOrInstrumentReference bound)
    (observationTimeReference receipt)
    (exactSpatialOrInstrumentCoordinateReference receipt)
    (contentIdentityOrHashReference receipt)
    (coverageReference receipt)
    (uncertaintyReference receipt)
    (provenanceReference receipt)
    (acquisitionAuthorityReference receipt)
    (rawEvidenceReference receipt)
    (providerInterpretationReference receipt)
    false refl
    false refl
    false refl
    (resultIdentityReference receipt)

------------------------------------------------------------------------
-- Introspective firewalls.
------------------------------------------------------------------------

data SensorObservationCreatesMechanism : Set where
data RemoteStressSignalCreatesDiagnosis : Set where
data SensorPrecisionCreatesWholeLESState : Set where
data SensorObservationCreatesCountryAuthority : Set where
data SensorObservationCreatesInterventionAuthority : Set where
data SharedObservationFusesKnowledgeHistories : Set where
data NoSensorMatchMeansNoEcologicalCondition : Set where

sensorObservationDoesNotCreateMechanism : SensorObservationCreatesMechanism → ⊥
sensorObservationDoesNotCreateMechanism ()

remoteStressSignalDoesNotCreateDiagnosis : RemoteStressSignalCreatesDiagnosis → ⊥
remoteStressSignalDoesNotCreateDiagnosis ()

sensorPrecisionDoesNotCreateWholeLESState : SensorPrecisionCreatesWholeLESState → ⊥
sensorPrecisionDoesNotCreateWholeLESState ()

sensorObservationDoesNotCreateCountryAuthority :
  SensorObservationCreatesCountryAuthority → ⊥
sensorObservationDoesNotCreateCountryAuthority ()

sensorObservationDoesNotCreateInterventionAuthority :
  SensorObservationCreatesInterventionAuthority → ⊥
sensorObservationDoesNotCreateInterventionAuthority ()

sharedObservationDoesNotFuseKnowledgeHistories :
  SharedObservationFusesKnowledgeHistories → ⊥
sharedObservationDoesNotFuseKnowledgeHistories ()

noSensorMatchDoesNotMeanNoEcologicalCondition :
  NoSensorMatchMeansNoEcologicalCondition → ⊥
noSensorMatchDoesNotMeanNoEcologicalCondition ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record LESSensorWorldAdapterBoundary : Set where
  constructor les-sensor-world-adapter-boundary
  field
    requestMustRemainLiveResidualBound : Bool
    requestMustRemainLiveResidualBoundIsTrue :
      requestMustRemainLiveResidualBound ≡ true
    calibrationAndBaselineRemainExplicit : Bool
    calibrationAndBaselineRemainExplicitIsTrue :
      calibrationAndBaselineRemainExplicit ≡ true
    mechanismMayRemainSplitAfterObservation : Bool
    mechanismMayRemainSplitAfterObservationIsTrue :
      mechanismMayRemainSplitAfterObservation ≡ true
    localKnowledgeAndAuthorityRemainIndependent : Bool
    localKnowledgeAndAuthorityRemainIndependentIsTrue :
      localKnowledgeAndAuthorityRemainIndependent ≡ true
    executedOutputMayEnterGenericAssessment : Bool
    executedOutputMayEnterGenericAssessmentIsTrue :
      executedOutputMayEnterGenericAssessment ≡ true
    noMatchMayEnterGenericAssessment : Bool
    noMatchMayEnterGenericAssessmentIsFalse :
      noMatchMayEnterGenericAssessment ≡ false
    adapterOwnsSemanticDisposition : Bool
    adapterOwnsSemanticDispositionIsFalse :
      adapterOwnsSemanticDisposition ≡ false
    adapterCreatesInterventionAuthority : Bool
    adapterCreatesInterventionAuthorityIsFalse :
      adapterCreatesInterventionAuthority ≡ false

canonicalLESSensorWorldAdapterBoundary : LESSensorWorldAdapterBoundary
canonicalLESSensorWorldAdapterBoundary =
  les-sensor-world-adapter-boundary
    true refl true refl true refl true refl true refl false refl false refl false refl
