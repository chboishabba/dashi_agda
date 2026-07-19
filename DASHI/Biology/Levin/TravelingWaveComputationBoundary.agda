module DASHI.Biology.Levin.TravelingWaveComputationBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record WaveCarrier (Position Phase Amplitude Frequency : Set) : Set where
  field
    phaseAt : Position → Phase
    amplitudeAt : Position → Amplitude
    frequency : Frequency
    travels : Bool

record WaveComputationWitness
  (Input Output WaveState : Set) : Set where
  field
    encode : Input → WaveState
    interact : WaveState → WaveState → WaveState
    decode : WaveState → Output
    reproducibleWithinContext : Bool
    superpositionPredictsOutput : Bool
    perturbingWaveChangesOutput : Bool

record TravelingWaveBoundary : Set where
  field
    standingAndTravelingSeparated : Bool
    fieldPropagationAndPeakVelocitySeparated : Bool
    correlationIsNotComputation : Bool
    lowDimensionalNeuralTrajectoryIsNotProofOfWaveCause : Bool
    causalPerturbationRequired : Bool
    analogComputationDoesNotExcludeDigitalSubprocesses : Bool
    interpretation : String

canonicalTravelingWaveBoundary : TravelingWaveBoundary
canonicalTravelingWaveBoundary = record
  { standingAndTravelingSeparated = true
  ; fieldPropagationAndPeakVelocitySeparated = true
  ; correlationIsNotComputation = true
  ; lowDimensionalNeuralTrajectoryIsNotProofOfWaveCause = true
  ; causalPerturbationRequired = true
  ; analogComputationDoesNotExcludeDigitalSubprocesses = true
  ; interpretation = "Traveling field patterns become computational only after an explicit encoding, interaction law, decoding and intervention-sensitive witness"
  }
