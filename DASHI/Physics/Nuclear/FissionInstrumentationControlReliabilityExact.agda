module DASHI.Physics.Nuclear.FissionInstrumentationControlReliabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- GENERIC AUTONOMOUS FISSION I&C SCIENCE
------------------------------------------------------------------------

data ICFunction : Set where
  sense
  conditionSignal
  estimateState
  compareToLimits
  actuate
  protect
  recordTelemetry
  diagnoseFault
  : ICFunction

record HarshEnvironmentEnvelope : Set where
  constructor harsh-environment-envelope
  field
    highTemperature : String
    ionizingRadiation : String
    displacementDamage : String
    longMissionLife : String
    limitedMaintenance : String
    compactMassVolume : String

open HarshEnvironmentEnvelope public

canonicalFissionEnvelope : HarshEnvironmentEnvelope
canonicalFissionEnvelope = harsh-environment-envelope
  "high-temperature in-core/ex-core operation"
  "total ionizing dose and transient radiation exposure"
  "neutron/proton displacement damage where applicable"
  "multi-year duty; FSP public material targets roughly decade-class operation"
  "failed remote reactor I&C may be difficult or impossible to service"
  "space systems penalise mass, volume, harnessing and redundant hardware"

record MeasurementControlLoop : Set where
  constructor measurement-control-loop
  field
    physicalQuantity : String
    transduction : String
    signalConditioning : String
    estimation : String
    decision : String
    actuation : String
    protection : String
    diagnosticRecord : String

open MeasurementControlLoop public

canonicalMeasurementControlLoop : MeasurementControlLoop
canonicalMeasurementControlLoop = measurement-control-loop
  "temperature, neutron flux, power, flow, pressure, position or related reactor state"
  "sensor converts physical state to electrical/optical measurable signal"
  "filter/amplify/linearise/digitise while preserving calibrated uncertainty"
  "combine signals/model state to estimate quantities not directly measured"
  "compare estimates and health state with command/limit logic"
  "drive control element, power conversion or supporting subsystem"
  "fault-tolerant trip/safe-state logic constrains hazardous states"
  "telemetry and health data support diagnosis and prognostics"

record QualificationChain : Set where
  constructor qualification-chain
  field
    componentCharacterisation : String
    radiationTesting : String
    thermalTesting : String
    combinedEnvironment : String
    ageingDrift : String
    calibration : String
    faultInjection : String
    systemValidation : String

open QualificationChain public

canonicalQualificationChain : QualificationChain
canonicalQualificationChain = qualification-chain
  "baseline transfer function, noise, bandwidth, resolution and failure modes"
  "TID/displacement/single-event response where relevant"
  "temperature cycling, gradients, dwell and survivability"
  "test interactions rather than assuming radiation and temperature effects superpose"
  "drift, embrittlement, insulation/sensor degradation and electronics ageing over mission life"
  "traceable mapping between signal and physical quantity with uncertainty"
  "verify detection, isolation, degraded operation and safe-state behaviour"
  "integrated hardware/software/control validation under representative plant dynamics"

record FissionICBoundary : Set where
  constructor fission-ic-boundary
  field
    radiationHardMeansMissionQualified : Bool
    radiationHardMeansMissionQualifiedIsFalse : radiationHardMeansMissionQualified ≡ false
    sensorSurvivesMeansControlLoopReliable : Bool
    sensorSurvivesMeansControlLoopReliableIsFalse : sensorSurvivesMeansControlLoopReliable ≡ false
    publicComponentSpecMeansQualifiedSystem : Bool
    publicComponentSpecMeansQualifiedSystemIsFalse : publicComponentSpecMeansQualifiedSystem ≡ false
    independentComponentReliabilityMultipliesNaively : Bool
    independentComponentReliabilityMultipliesNaivelyIsFalse : independentComponentReliabilityMultipliesNaively ≡ false
    nominalCalibrationMeansEndOfLifeCalibration : Bool
    nominalCalibrationMeansEndOfLifeCalibrationIsFalse : nominalCalibrationMeansEndOfLifeCalibration ≡ false

canonicalFissionICBoundary : FissionICBoundary
canonicalFissionICBoundary = fission-ic-boundary
  false refl
  false refl
  false refl
  false refl
  false refl

data FissionICReverseTarget : Set where
  needEnvironmentSpectrum
  needFailureRateModel
  needCommonCauseModel
  needCalibrationDriftData
  needFaultToleranceArchitecture
  needIntegratedQualificationReceipt
  : FissionICReverseTarget
