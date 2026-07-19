module DASHI.Biology.Levin.MixedSelectivityFieldControl where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record MixedSelectivitySystem
  (Neuron Context Stimulus Response FieldPattern : Set) : Set where
  field
    respond : Neuron → Context → Stimulus → Response
    fieldGate : FieldPattern → Neuron → Bool
    contextPattern : Context → FieldPattern
    sameStimulusMayChangeWithContext : Bool
    gateActsOnPopulationNotSingleSynapse : Bool
    fieldPatternDoesNotUniquelyDetermineResponse : Bool
    interpretation : String

record ContextDependentWitness
  {Neuron Context Stimulus Response FieldPattern : Set}
  (S : MixedSelectivitySystem Neuron Context Stimulus Response FieldPattern) : Set where
  field
    neuron : Neuron
    first second : Context
    stimulus : Stimulus
    responsesDiffer : Bool

record FieldControlBoundary : Set where
  field
    mixedSelectivityObserved : Bool
    oscillatoryFieldCorrelatesWithContext : Bool
    interventionSensitiveFieldEffectRequired : Bool
    connectionWeightsRemainRelevant : Bool
    fieldControlIsNotHomunculus : Bool
    fieldControlDoesNotImplyConsciousness : Bool

canonicalFieldControlBoundary : FieldControlBoundary
canonicalFieldControlBoundary = record
  { mixedSelectivityObserved = true
  ; oscillatoryFieldCorrelatesWithContext = true
  ; interventionSensitiveFieldEffectRequired = true
  ; connectionWeightsRemainRelevant = true
  ; fieldControlIsNotHomunculus = true
  ; fieldControlDoesNotImplyConsciousness = true
  }
