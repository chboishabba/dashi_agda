module DASHI.Biology.Levin.BoundaryHiddenStateNonrecurrence where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record BoundaryObservation : Set where
  field
    sameObservedInput : Bool
    sameObservedOutput : Bool

record HiddenStateDivergenceWitness : Set where
  field
    observation : BoundaryObservation
    distinctInternalHistories : Bool
    distinctInternalStates : Bool
    boundaryBehaviourRecurred : Bool

record NonrecurrenceBoundary : Set where
  field
    sameBehaviourDoesNotForceSameInterior : Bool
    finiteInputOutputDoesNotIdentifyMachine : Bool
    hiddenStateMayCarryMemoryOrContext : Bool
    hiddenStateIsNotAutomaticallySemanticMemory : Bool
    interpretation : String

canonicalNonrecurrenceBoundary : NonrecurrenceBoundary
canonicalNonrecurrenceBoundary = record
  { sameBehaviourDoesNotForceSameInterior = true
  ; finiteInputOutputDoesNotIdentifyMachine = true
  ; hiddenStateMayCarryMemoryOrContext = true
  ; hiddenStateIsNotAutomaticallySemanticMemory = true
  ; interpretation = "A low-dimensional biological boundary can recur while the higher-dimensional internal state and history do not"
  }
