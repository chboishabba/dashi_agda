module DASHI.Biology.DrosophilaMotorEffectorPhysiologyBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.DrosophilaMaleCNSEffectorObservationBridge as Fly

------------------------------------------------------------------------
-- Concrete sources for the CNS-output -> muscle/effector -> kinematics seam.
------------------------------------------------------------------------

azevedoMotorAtlasSource : Fly.ScientificSourceReceipt
azevedoMotorAtlasSource =
  Fly.scientificSourceReceipt
    "Azevedo et al."
    "Connectomic reconstruction of a female Drosophila ventral nerve cord"
    "DOI:10.1038/s41586-024-07389-x"
    "Adult Drosophila VNC connectome with mapped leg and wing motor-neuron muscle targets using genetic driver lines and X-ray holographic nanotomography."

lesserPremotorSource : Fly.ScientificSourceReceipt
lesserPremotorSource =
  Fly.scientificSourceReceipt
    "Lesser, Azevedo, Phelps et al."
    "Synaptic architecture of leg and wing premotor control networks in Drosophila"
    "DOI:10.1038/s41586-024-07600-z"
    "Premotor network modules link motor neurons to muscles with related functions; leg and wing systems show distinct recruitment architectures."

schnellWingMuscleSource : Fly.ScientificSourceReceipt
schnellWingMuscleSource =
  Fly.scientificSourceReceipt
    "Schnell, Weir, Roth, Fairhall, Dickinson"
    "The Function and Organization of the Motor System Controlling Flight Maneuvers in Flies"
    "DOI:10.1016/j.cub.2016.12.018"
    "In vivo imaging of the complete wing-control muscle ensemble during flight, relating muscle activity to aerodynamically functional wing motion."

lehmannActivationSource : Fly.ScientificSourceReceipt
lehmannActivationSource =
  Fly.scientificSourceReceipt
    "Lehmann, Götz"
    "Activation phase ensures kinematic efficacy in flight-steering muscles of Drosophila melanogaster"
    "DOI:10.1007/BF00194985"
    "Steering-muscle spike timing is related to ipsilateral wing-beat amplitude and flight force."

proprioceptionBiomechanicsSource : Fly.ScientificSourceReceipt
proprioceptionBiomechanicsSource =
  Fly.scientificSourceReceipt
    "Mamiya et al."
    "Biomechanical origins of proprioceptor feature selectivity and topographic maps in the Drosophila leg"
    "DOI:10.1016/j.neuron.2023.07.009"
    "Leg biomechanics transform joint movement into proprioceptive signals, providing a concrete body-state -> sensory-return producer."

motorEffectorSources : List Fly.ScientificSourceReceipt
motorEffectorSources =
  azevedoMotorAtlasSource
  ∷ lesserPremotorSource
  ∷ schnellWingMuscleSource
  ∷ lehmannActivationSource
  ∷ proprioceptionBiomechanicsSource
  ∷ []

------------------------------------------------------------------------
-- Motor-to-effector carrier.
------------------------------------------------------------------------

data EffectorSubsystem : Set where
  legSystem : EffectorSubsystem
  wingSteeringSystem : EffectorSubsystem
  wingPowerSystem : EffectorSubsystem
  proboscisSystem : EffectorSubsystem
  abdominalSystem : EffectorSubsystem

data MotorEffectorBoundary : Set where
  noSynapseCountEqualsMuscleActivation : MotorEffectorBoundary
  noMotorNeuronIdentityEqualsForce : MotorEffectorBoundary
  noMuscleActivationEqualsKinematics : MotorEffectorBoundary
  noKinematicsEqualsAerodynamicForce : MotorEffectorBoundary
  noSensoryReturnWithoutMechanics : MotorEffectorBoundary

record MotorEffectorPhysiologySurface : Set₁ where
  field
    MotorNeuron : Set
    Muscle : Set
    MotorSpikeTrain : Set
    MuscleActivation : Set
    MuscleForce : Set
    JointOrWingKinematics : Set
    ExternalForce : Set
    ProprioceptiveReturn : Set

    muscleTarget : MotorNeuron → Muscle
    activationFromMotor : MotorSpikeTrain → MuscleActivation
    forceFromActivation : MuscleActivation → MuscleForce
    kinematicsFromForce : MuscleForce → JointOrWingKinematics
    externalForceFromKinematics : JointOrWingKinematics → ExternalForce
    sensoryReturnFromKinematics : JointOrWingKinematics → ProprioceptiveReturn

    motorAtlasReceipt : Fly.ScientificSourceReceipt
    activationReceipt : Fly.ScientificSourceReceipt
    biomechanicsReceipt : Fly.ScientificSourceReceipt
    sensoryReturnReceipt : Fly.ScientificSourceReceipt

open MotorEffectorPhysiologySurface public

record EffectorClosureStatus : Set where
  field
    motorTargetMapReceipted : Bool
    muscleActivationReceipted : Bool
    biomechanicsReceipted : Bool
    sensoryReturnReceipted : Bool

    fullEffectorClosureClaim : Bool
    fullEffectorClosureClaimIsFalse :
      fullEffectorClosureClaim ≡ false

    reading : String

open EffectorClosureStatus public

canonicalEffectorClosureStatus : EffectorClosureStatus
canonicalEffectorClosureStatus =
  record
    { motorTargetMapReceipted = true
    ; muscleActivationReceipted = true
    ; biomechanicsReceipted = true
    ; sensoryReturnReceipted = true
    ; fullEffectorClosureClaim = false
    ; fullEffectorClosureClaimIsFalse = refl
    ; reading =
        "The programme now has separately attributed producers for motor-neuron muscle targets, muscle activation, movement biomechanics, and proprioceptive return; this does not yet mean every MaleCNS effector coordinate is empirically closed."
    }

canonicalMotorEffectorBoundaries : List MotorEffectorBoundary
canonicalMotorEffectorBoundaries =
  noSynapseCountEqualsMuscleActivation
  ∷ noMotorNeuronIdentityEqualsForce
  ∷ noMuscleActivationEqualsKinematics
  ∷ noKinematicsEqualsAerodynamicForce
  ∷ noSensoryReturnWithoutMechanics
  ∷ []
