module DASHI.Physics.QuantumSensors.SuperconductingRotorSIExperimentRegimeExact where

-- A typed measured-regime socket, NOT a gravitational coupling theorem.
-- Physical SI owner: DASHI.Physics.Units.SI, BIPM SI Brochure, 2026 rev.
-- Mathematical experiments are verified in
-- scripts/check_sc_rotor_filsinger_physical.py (SymPy only).
--
-- Original apparatus data: Hathaway et al Physica C 385 (2003) 488-500;
-- Graham et al Physica C 468 (2008); Tajmar et al arXiv:0707.3806.
-- Repo donors: SmithFilsinger material/source-port ledgers and
-- ExoticGravity LiTorr source/constitutive / constraint registries.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Int using (pos)
open import Agda.Builtin.String using (String)
import DASHI.Physics.Units.SI as SI

-- Radians are dimensionless in coherent SI; rad/s has frequency dimension.
AngularVelocity : SI.Dimension
AngularVelocity = SI.Frequency

AngularAcceleration : SI.Dimension
AngularAcceleration =
  SI.dim SI.zeroI SI.zeroI SI.minusTwo SI.zeroI
         SI.zeroI SI.zeroI SI.zeroI

MomentOfInertia : SI.Dimension
MomentOfInertia =
  SI.dim (pos 2) SI.one SI.zeroI SI.zeroI
         SI.zeroI SI.zeroI SI.zeroI

-- Reading rotation, RF pump, trapped flux, cryogenic phase and mechanical
-- response on one synchronized apparatus. Observation provenance is mandatory
-- because dimensional equality is NOT a calibration or physical law.
record RotorSIObservation : Set where
  field
    rotationRate : SI.Measurement AngularVelocity SI.unitScale
    angularAcceleration : SI.Measurement AngularAcceleration SI.unitScale
    sourceDiskTemperature : SI.Measurement SI.Temperature SI.unitScale
    phaseTransitionTemperature : SI.Measurement SI.Temperature SI.unitScale
    rfPumpFrequency : SI.Measurement SI.Frequency SI.unitScale
    rfPumpPower : SI.Measurement SI.Power SI.unitScale
    trappedFlux : SI.Measurement SI.MagneticFlux SI.unitScale
    diskRadius : SI.Measurement SI.Length SI.unitScale
    momentOfInertia : SI.Measurement MomentOfInertia SI.unitScale
    measuredTestMassForce : SI.Measurement SI.Force SI.unitScale
    observedMagneticField : SI.Measurement SI.MagneticFluxDensity SI.unitScale
    observationTime : SI.Measurement SI.Time SI.unitScale
    actualMechanicalRotationReversed : Bool
    rfPhaseReversed : Bool
    phaseStateMeasured : Bool
    sourceAndBackgroundsCalibrated : Bool
    rawDataSource : String
    calibrationVersion : String

-- Distinct test channels should not be conflated.
data ProbeChannel : Set where
  staticWeight : ProbeChannel
  externalGyroscope : ProbeChannel
  tangentialAccelerometer : ProbeChannel
  magneticField : ProbeChannel

data SourceWorld : Set where
  ordinaryElectromagneticAndMechanical : SourceWorld
  changedSuperconductorSource : SourceWorld
  changedConstitutiveResponse : SourceWorld

record MatchedExperiment : Set where
  field
    baseline : RotorSIObservation
    treatment : RotorSIObservation
    sensorChannel : ProbeChannel
    modelWorld : SourceWorld
    sameGeometry : Set
    sameInstrumentCalibration : Set
    signedSourcePowerAudit : Set
    nuisanceClosure : Set
    geometryWitness : sameGeometry
    calibrationWitness : sameInstrumentCalibration
    powerWitness : signedSourcePowerAudit
    nuisanceWitness : nuisanceClosure

-- Exact SI namespace equalities; these are not gravitational-effect proofs.
angularRateHasFrequencyDimension :
  AngularVelocity ≡ SI.Frequency
angularRateHasFrequencyDimension = refl

-- A reported gyro response cannot be silently substituted for a weight
-- measurement: the constructors are definitionally distinct.
data DifferentProbeChannels : Set where

weightIsNotGyroscope : staticWeight ≡ externalGyroscope →
                       DifferentProbeChannels
weightIsNotGyroscope ()
