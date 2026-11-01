module DASHI.Core.RelationalObserverGainExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Generic observer-gain owner.
--
-- A small physical perturbation may remain physically small while a richer
-- relational observer maps it to a more discriminable output.  This is
-- sensitivity/readout amplification, not automatic dynamical amplification.
------------------------------------------------------------------------

record RelationalObserverGain : Set₁ where
  field
    FineState : Set
    CoarseObservation : Set
    RefinedObservation : Set

    coarseObserve : FineState → CoarseObservation
    refinedObserve : FineState → RefinedObservation

    PerturbationPair : Set
    unperturbed : PerturbationPair → FineState
    perturbed : PerturbationPair → FineState

    coarseIndistinguishable : PerturbationPair → Set
    refinedDistinguishable : PerturbationPair → Set

    gainReading : String

open RelationalObserverGain public

record ObserverGainWitness (surface : RelationalObserverGain) : Set where
  field
    pair : PerturbationPair surface
    coarseWitness : coarseIndistinguishable surface pair
    refinedWitness : refinedDistinguishable surface pair

open ObserverGainWitness public

data ToyFineState : Set where
  baselineFineState : ToyFineState
  tinyPerturbedFineState : ToyFineState

data ToyCoarseObservation : Set where
  coarseSame : ToyCoarseObservation

data ToyRefinedObservation : Set where
  refinedBaseline : ToyRefinedObservation
  refinedPerturbed : ToyRefinedObservation

data ToyPerturbationPair : Set where
  tinyPerturbationPair : ToyPerturbationPair

data ToyCoarseIndistinguishable : ToyPerturbationPair → Set where
  tinyPerturbationCoarseSame :
    ToyCoarseIndistinguishable tinyPerturbationPair

data ToyRefinedDistinguishable : ToyPerturbationPair → Set where
  tinyPerturbationRefinedSeparate :
    ToyRefinedDistinguishable tinyPerturbationPair

canonicalRelationalObserverGain : RelationalObserverGain
canonicalRelationalObserverGain =
  record
    { FineState = ToyFineState
    ; CoarseObservation = ToyCoarseObservation
    ; RefinedObservation = ToyRefinedObservation
    ; coarseObserve = λ _ → coarseSame
    ; refinedObserve = λ
        { baselineFineState → refinedBaseline
        ; tinyPerturbedFineState → refinedPerturbed
        }
    ; PerturbationPair = ToyPerturbationPair
    ; unperturbed = λ _ → baselineFineState
    ; perturbed = λ _ → tinyPerturbedFineState
    ; coarseIndistinguishable = ToyCoarseIndistinguishable
    ; refinedDistinguishable = ToyRefinedDistinguishable
    ; gainReading =
        "A relationally enriched observer may distinguish a fine perturbation that a coarser observer identifies, without increasing the underlying perturbation itself."
    }

canonicalObserverGainWitness :
  ObserverGainWitness canonicalRelationalObserverGain
canonicalObserverGainWitness =
  record
    { pair = tinyPerturbationPair
    ; coarseWitness = tinyPerturbationCoarseSame
    ; refinedWitness = tinyPerturbationRefinedSeparate
    }

refinedObservationActuallySeparatesToyStates :
  refinedObserve canonicalRelationalObserverGain baselineFineState
  ≡
  refinedObserve canonicalRelationalObserverGain tinyPerturbedFineState
  → ⊥
refinedObservationActuallySeparatesToyStates ()

coarseObservationCollapsesToyStates :
  coarseObserve canonicalRelationalObserverGain baselineFineState
  ≡
  coarseObserve canonicalRelationalObserverGain tinyPerturbedFineState
coarseObservationCollapsesToyStates = refl

record RelationalObserverGainBoundary : Set where
  constructor relationalObserverGainBoundary
  field
    observerGainMeansLargerPhysicalPerturbation : Bool
    observerGainMeansLargerPhysicalPerturbationIsFalse :
      observerGainMeansLargerPhysicalPerturbation ≡ false

    couplingMeansEntanglement : Bool
    couplingMeansEntanglementIsFalse :
      couplingMeansEntanglement ≡ false

    refinedObservationChangesUnderlyingDynamicsByDefinition : Bool
    refinedObservationChangesUnderlyingDynamicsByDefinitionIsFalse :
      refinedObservationChangesUnderlyingDynamicsByDefinition ≡ false

canonicalRelationalObserverGainBoundary : RelationalObserverGainBoundary
canonicalRelationalObserverGainBoundary =
  relationalObserverGainBoundary
    false refl
    false refl
    false refl
