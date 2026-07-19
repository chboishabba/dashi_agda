module DASHI.Biology.Levin.NeuralWaveAnalogComputation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record WaveInteractionModel
  (Wave State Output : Set) : Set where
  field
    superpose : Wave → Wave → Wave
    readState : Wave → State
    interpretOutput : Wave → Output
    parallelInteractionAvailable : Bool
    continuousAmplitudeAvailable : Bool
    interpretation : String

record ComputationRealisationWitness
  {Wave State Output : Set}
  (M : WaveInteractionModel Wave State Output) : Set where
  field
    inputEncodingSpecified : Bool
    operationSpecified : Bool
    outputDecodingSpecified : Bool
    commutingInterpretationDiagram : Bool
    perturbationPreservesPredictedRelation : Bool

record RecoveryTrajectoryWitness : Set where
  field
    distractionDisplacesPopulationState : Bool
    fieldTrajectoryTracksRecovery : Bool
    successfulAndFailedTrialsDiscriminate : Bool
    fieldPerturbationChangesRecovery : Bool

record AnalogComputationBoundary : Set where
  field
    waveSuperpositionAloneIsNotComputation : Bool
    lowDimensionalTrajectoryDoesNotProveFieldCause : Bool
    efficientAnalogReadingRequiresEnergyAccounting : Bool
    neuralAnalogComputationDoesNotExcludeDigitalLikeSubprocesses : Bool
    computationDoesNotImplyConsciousExperience : Bool

canonicalAnalogComputationBoundary : AnalogComputationBoundary
canonicalAnalogComputationBoundary = record
  { waveSuperpositionAloneIsNotComputation = true
  ; lowDimensionalTrajectoryDoesNotProveFieldCause = true
  ; efficientAnalogReadingRequiresEnergyAccounting = true
  ; neuralAnalogComputationDoesNotExcludeDigitalLikeSubprocesses = true
  ; computationDoesNotImplyConsciousExperience = true
  }
