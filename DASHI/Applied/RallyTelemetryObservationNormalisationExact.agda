module DASHI.Applied.RallyTelemetryObservationNormalisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Applied.RallyReccePaceNoteFibreOverTimeExact as Rally
import DASHI.Core.ObservationInterventionTrustFibreExact as Trust

------------------------------------------------------------------------
-- RALLY TELEMETRY NORMALISATION
--
-- Raw game / hardware / video observations are not the rally state.  This
-- owner gives a canonical ABI that preserves source, clock and provenance while
-- adapting heterogeneous simulator streams into the observation fibre.
------------------------------------------------------------------------

data TelemetrySource : Set where
  simHub : TelemetrySource
  gameNativeUdp : TelemetrySource
  beamNGApi : TelemetrySource
  wheelPedalHardware : TelemetrySource
  renderedVideoCapture : TelemetrySource
  paceCallAudio : TelemetrySource
  realVehicleLogger : TelemetrySource
  privilegedSimulatorTruth : TelemetrySource

data CanonicalSignal : Set where
  simulationTime : CanonicalSignal
  frameIndex : CanonicalSignal
  stageDistance : CanonicalSignal
  position : CanonicalSignal
  orientation : CanonicalSignal
  linearVelocity : CanonicalSignal
  angularVelocity : CanonicalSignal
  linearAcceleration : CanonicalSignal
  steeringInput : CanonicalSignal
  throttleInput : CanonicalSignal
  brakeInput : CanonicalSignal
  clutchInput : CanonicalSignal
  gear : CanonicalSignal
  engineSpeed : CanonicalSignal
  wheelSpeed : CanonicalSignal
  suspensionPosition : CanonicalSignal
  suspensionVelocity : CanonicalSignal
  tyreSlip : CanonicalSignal
  tyreLoad : CanonicalSignal
  tyreTemperature : CanonicalSignal
  surfaceHint : CanonicalSignal
  paceCallToken : CanonicalSignal
  renderedFrame : CanonicalSignal

data ProvenanceStrength : Set where
  nativeReported : ProvenanceStrength
  hardwareMeasured : ProvenanceStrength
  derivedEstimate : ProvenanceStrength
  synchronisedEstimate : ProvenanceStrength
  privilegedGroundTruth : ProvenanceStrength
  unresolvedProvenance : ProvenanceStrength

record RawTelemetrySample : Set where
  constructor raw-telemetry-sample
  field
    source : TelemetrySource
    sourceField : String
    rawValueReference : String
    sourceClockReference : String
    sourceFrameReference : String
    provenanceStrength : ProvenanceStrength
    provenanceReference : String

open RawTelemetrySample public

record NormalisedTelemetrySample : Set where
  constructor normalised-telemetry-sample
  field
    signal : CanonicalSignal
    canonicalValueReference : String
    canonicalTimeReference : String
    canonicalStationReference : String
    sourceReceipt : RawTelemetrySample
    normalisationReference : String

open NormalisedTelemetrySample public

------------------------------------------------------------------------
-- Adapter contract.  Normalisation may change representation/unit but may not
-- manufacture a source, clock or provenance strength.
------------------------------------------------------------------------

record TelemetryAdapterContract : Set₁ where
  constructor telemetry-adapter-contract
  field
    Raw : Set
    Normalised : Set
    adapt : Raw → Normalised
    adapterReference : String
    sourceIdentityRetained : Bool
    sourceIdentityRetainedIsTrue : sourceIdentityRetained ≡ true
    clockLineageRetained : Bool
    clockLineageRetainedIsTrue : clockLineageRetained ≡ true
    provenanceRetained : Bool
    provenanceRetainedIsTrue : provenanceRetained ≡ true

------------------------------------------------------------------------
-- Synchronisation receipt.  Alignment is an explicit inferred relationship
-- among clocks/frames/stage-station, not equality of their source timestamps.
------------------------------------------------------------------------

record SynchronisationReceipt : Set where
  constructor synchronisation-receipt
  field
    masterClockReference : String
    videoClockReference : String
    telemetryClockReference : String
    controlClockReference : String
    paceCallClockReference : String
    stationAlignmentReference : String
    alignmentMethodReference : String
    uncertaintyReference : String
    alignmentIsEstimatedNotDefinitional : Bool
    alignmentIsEstimatedNotDefinitionalIsTrue :
      alignmentIsEstimatedNotDefinitional ≡ true

record SynchronousTraversalObservation : Set where
  constructor synchronous-traversal-observation
  field
    traversalReference : String
    stationReference : String
    videoReference : String
    telemetryReference : String
    controlReference : String
    paceCallReference : String
    syncReceipt : SynchronisationReceipt

------------------------------------------------------------------------
-- Trust donor: reported telemetry and physical state remain separable.
------------------------------------------------------------------------

observationTrustBoundary : Trust.ObservationInterventionTrustBoundary
observationTrustBoundary = Trust.canonicalObservationInterventionTrustBoundary

------------------------------------------------------------------------
-- Deployment / validation boundary.
------------------------------------------------------------------------

data NormalisedTelemetryEqualsPhysicalTruthPermission : Set where
data SynchronisedTimestampEqualsExactEventTimePermission : Set where
data PrivilegedTruthMayEnterDeployableObservationPermission : Set where

normalisedTelemetryDoesNotBecomePhysicalTruth :
  NormalisedTelemetryEqualsPhysicalTruthPermission → ⊥
normalisedTelemetryDoesNotBecomePhysicalTruth ()

synchronisationDoesNotClaimExactEventTime :
  SynchronisedTimestampEqualsExactEventTimePermission → ⊥
synchronisationDoesNotClaimExactEventTime ()

privilegedTruthStaysValidationOnly :
  PrivilegedTruthMayEnterDeployableObservationPermission → ⊥
privilegedTruthStaysValidationOnly ()

------------------------------------------------------------------------
-- Canonical boundary for the next executable producer.
------------------------------------------------------------------------

record RallyTelemetryNormalisationBoundary : Set where
  constructor rally-telemetry-normalisation-boundary
  field
    oneCanonicalAbiAcrossSources : Bool
    oneCanonicalAbiAcrossSourcesIsTrue : oneCanonicalAbiAcrossSources ≡ true
    sourceProvenanceSurvivesNormalisation : Bool
    sourceProvenanceSurvivesNormalisationIsTrue :
      sourceProvenanceSurvivesNormalisation ≡ true
    synchronisationIsExplicitReceipt : Bool
    synchronisationIsExplicitReceiptIsTrue : synchronisationIsExplicitReceipt ≡ true
    privilegedTruthIsDeployableInput : Bool
    privilegedTruthIsDeployableInputIsFalse : privilegedTruthIsDeployableInput ≡ false

canonicalRallyTelemetryNormalisationBoundary : RallyTelemetryNormalisationBoundary
canonicalRallyTelemetryNormalisationBoundary =
  rally-telemetry-normalisation-boundary
    true refl
    true refl
    true refl
    false refl
