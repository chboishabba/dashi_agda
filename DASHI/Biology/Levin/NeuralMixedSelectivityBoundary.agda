module DASHI.Biology.Levin.NeuralMixedSelectivityBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record MixedSelectivitySystem
  (Neuron Stimulus Context Response : Set) : Set where
  field
    response : Neuron → Stimulus → Context → Response
    sameStimulusMayChangeWithContext : Bool
    oneNeuronMayParticipateInSeveralCodes : Bool
    populationCodeMayBeLowerDimensional : Bool
    interpretation : String

record ContextReversalWitness
  {Neuron Stimulus Context Response : Set}
  (S : MixedSelectivitySystem Neuron Stimulus Context Response) : Set where
  field
    neuron : Neuron
    stimulus : Stimulus
    first second : Context
    responseDiffers : Bool

record MixedSelectivityClaimBoundary : Set where
  field
    multifunctionalDoesNotMeanArbitrary : Bool
    contextDependenceDoesNotImplyConsciousness : Bool
    lowDimensionalPopulationCodeDoesNotIdentifyMechanism : Bool
    distributedCodeDoesNotProveUnlimitedCapacity : Bool

canonicalMixedSelectivityClaimBoundary : MixedSelectivityClaimBoundary
canonicalMixedSelectivityClaimBoundary = record
  { multifunctionalDoesNotMeanArbitrary = true
  ; contextDependenceDoesNotImplyConsciousness = true
  ; lowDimensionalPopulationCodeDoesNotIdentifyMechanism = true
  ; distributedCodeDoesNotProveUnlimitedCapacity = true
  }
