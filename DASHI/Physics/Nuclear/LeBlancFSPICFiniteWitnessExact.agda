module DASHI.Physics.Nuclear.LeBlancFSPICFiniteWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Nuclear.LeBlancFissionSurfacePowerICBidiExact as L

record FiniteLeBlancFSPICWitness : Set where
  constructor finite-leblanc-fspic-witness
  field
    sourceReference : String
    region : L.FSPSystemRegion
    sourceRanges : List L.SourceRange
    sensorKinds : List L.ICSensorKind
    requiredFunctions : List L.ICFunction
    notionalSourceEnvelope : Bool
    flightQualificationPaid : Bool
    nextExactLeaf : String

open FiniteLeBlancFSPICWitness public

finiteLeBlancFSPICWitness : FiniteLeBlancFSPICWitness
finiteLeBlancFSPICWitness = finite-leblanc-fspic-witness
  "NASA NTRS 20250008475"
  L.inCore
  (L.inCoreTemperature ∷ L.inCoreNeutronFlux ∷ L.inCoreNeutronFluence ∷
   L.inCoreGammaDose ∷ L.pressureSensorPressureRange ∷ L.flowSensorMassFlowRange ∷ [])
  (L.temperatureSensor ∷ L.pressureSensor ∷ L.flowSensor ∷ L.radiationDetector ∷ [])
  (L.measureState ∷ L.selfDiagnosis ∷ L.faultDetection ∷ L.communicateState ∷
   L.automatedFaultResponse ∷ L.processControl ∷ [])
  true
  false
  "recover source-exact device-level candidate/qualification/failure receipts and close one finite sensor-to-autonomous-response chain"

finiteWitnessIsSourceExactNotionalEnvelope : Bool
finiteWitnessIsSourceExactNotionalEnvelope = true

notionalEnvelopeIsFlightQualification : Bool
notionalEnvelopeIsFlightQualification = false

finiteWitnessPaysUniqueSensorSelection : Bool
finiteWitnessPaysUniqueSensorSelection = false
