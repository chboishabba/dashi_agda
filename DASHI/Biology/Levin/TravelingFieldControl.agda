module DASHI.Biology.Levin.TravelingFieldControl where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record TravelingFieldSystem
  (Location Time Phase Amplitude Excitability : Set) : Set where
  field
    phaseAt : Location → Time → Phase
    amplitudeAt : Location → Time → Amplitude
    excitabilityAt : Location → Time → Excitability
    fieldModulatesSpikeTiming : Bool
    fieldPatternMovesAcrossCarrier : Bool
    contextCanSelectFieldPattern : Bool
    interpretation : String

record MovingStencilWitness
  {Location Time Phase Amplitude Excitability : Set}
  (S : TravelingFieldSystem Location Time Phase Amplitude Excitability) : Set where
  field
    first second : Time
    location : Location
    permittedAtFirst : Bool
    permittedAtSecond : Bool
    changedPermission : Bool

record FieldControlBoundary : Set where
  field
    correlationDoesNotEstablishCausalControl : Bool
    causalFieldEffectRequiresPerturbation : Bool
    travelingWaveDoesNotByItselfCompute : Bool
    organizedWaveDoesNotByItselfEncodeGoal : Bool
    fieldControlDoesNotReplaceSynapticDynamics : Bool

canonicalFieldControlBoundary : FieldControlBoundary
canonicalFieldControlBoundary = record
  { correlationDoesNotEstablishCausalControl = true
  ; causalFieldEffectRequiresPerturbation = true
  ; travelingWaveDoesNotByItselfCompute = true
  ; organizedWaveDoesNotByItselfEncodeGoal = true
  ; fieldControlDoesNotReplaceSynapticDynamics = true
  }
