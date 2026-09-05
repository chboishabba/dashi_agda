module DASHI.Law.LowTraceCoerciveForceNonReconstructionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.IntersectionalNonFactorability as NF

------------------------------------------------------------------------
-- Force history and later observable record are deliberately distinct.
------------------------------------------------------------------------

data ForceKind : Set where
  noForce physicalControl conductedElectricalContact projectileElectrical : ForceKind

data TraceState : Set where
  noTrace transientTrace durableTrace : TraceState

data RecordingState : Set where
  noRecording cameraOff cameraOn partialRecording : RecordingState

record ForceHypervoxel : Set where
  constructor forceHypervoxel
  field
    forceKind : ForceKind
    trace : TraceState
    recording : RecordingState
    telemetryAvailable : Bool
    independentWitness : Bool
    medicalEvidence : Bool
    officerReportPresent : Bool
    subjectReportPresent : Bool
    sourceReference : String

open ForceHypervoxel public

record ObservableRecord : Set where
  constructor observableRecord
  field
    observedTrace : TraceState
    observedRecording : RecordingState
    observedTelemetry : Bool
    observedWitness : Bool
    observedMedicalEvidence : Bool

open ObservableRecord public

observe : ForceHypervoxel → ObservableRecord
observe h = observableRecord
  (trace h)
  (recording h)
  (telemetryAvailable h)
  (independentWitness h)
  (medicalEvidence h)

actualForce : ForceHypervoxel → ForceKind
actualForce = forceKind

------------------------------------------------------------------------
-- Concrete information-theoretic witness: distinct force histories can map to
-- the same coarse post-encounter evidentiary record.
------------------------------------------------------------------------

noForceLowRecord : ForceHypervoxel
noForceLowRecord = forceHypervoxel
  noForce noTrace noRecording false false false true true
  "abstract low-observability witness: no force"

contactElectricalLowRecord : ForceHypervoxel
contactElectricalLowRecord = forceHypervoxel
  conductedElectricalContact noTrace noRecording false false false true true
  "abstract low-observability witness: contact electrical force"

sameObservableRecord : observe noForceLowRecord ≡ observe contactElectricalLowRecord
sameObservableRecord = refl

differentForceHistory : actualForce noForceLowRecord ≡ actualForce contactElectricalLowRecord → ⊥
differentForceHistory ()

forceHistoryNonFactorability : NF.NonFactorabilityWitness observe actualForce
forceHistoryNonFactorability =
  NF.nonFactorabilityWitness
    noForceLowRecord contactElectricalLowRecord
    sameObservableRecord differentForceHistory

postEncounterRecordCannotReconstructForceHistory :
  NF.FactorsThrough observe actualForce → ⊥
postEncounterRecordCannotReconstructForceHistory =
  NF.witnessRulesOutEveryFlatFactorisation forceHistoryNonFactorability

------------------------------------------------------------------------
-- Audit channels are independent fibres; absence of one channel must not be
-- silently promoted into absence of the underlying force event.
------------------------------------------------------------------------

record AuditChannels : Set where
  constructor auditChannels
  field
    physicalTrace bodyCamera deviceTelemetry thirdPartyWitness medicalTrace : Bool

open AuditChannels public

record AuditabilityBoundary : Set where
  constructor auditabilityBoundary
  field
    absenceOfRecordedEvidenceMeansNoForce : Bool
    absenceOfRecordedEvidenceMeansNoForceIsFalse :
      absenceOfRecordedEvidenceMeansNoForce ≡ false
    deliveryGeometryDeterminesRiskClass : Bool
    deliveryGeometryDeterminesRiskClassIsFalse :
      deliveryGeometryDeterminesRiskClass ≡ false
    marketingClassificationDeterminesFunctionalClass : Bool
    marketingClassificationDeterminesFunctionalClassIsFalse :
      marketingClassificationDeterminesFunctionalClass ≡ false

canonicalAuditabilityBoundary : AuditabilityBoundary
canonicalAuditabilityBoundary = auditabilityBoundary false refl false refl false refl

------------------------------------------------------------------------
-- Electrical coercive devices share a functional carrier while retaining
-- delivery geometry as a separate coordinate.
------------------------------------------------------------------------

data DeliveryGeometry : Set where
  directContact firedProbes : DeliveryGeometry

record ElectricalCoerciveDevice : Set where
  constructor electricalCoerciveDevice
  field
    deliveryGeometry : DeliveryGeometry
    electricalEnergyAppliedToPerson : Bool
    painOrMotorInterferenceIntended : Bool
    seriousInjuryOrDeathWarning : Bool
    automaticTelemetry : Bool
    functionalReference : String

open ElectricalCoerciveDevice public

gloveFunctionalCarrier : ElectricalCoerciveDevice
gloveFunctionalCarrier = electricalCoerciveDevice
  directContact true true true false
  "G.L.O.V.E. functional CEW carrier; exact telemetry capability requires device-specific receipt"

probeCEWFunctionalCarrier : ElectricalCoerciveDevice
probeCEWFunctionalCarrier = electricalCoerciveDevice
  firedProbes true true true true
  "projectile conducted-electrical-weapon comparison carrier"

sameElectricalCoerciveSuperclass :
  electricalEnergyAppliedToPerson gloveFunctionalCarrier ≡
  electricalEnergyAppliedToPerson probeCEWFunctionalCarrier
sameElectricalCoerciveSuperclass = refl

differentDeliveryGeometry :
  deliveryGeometry gloveFunctionalCarrier ≡ deliveryGeometry probeCEWFunctionalCarrier → ⊥
differentDeliveryGeometry ()
