module DASHI.Biology.Levin.MixedSelectivityWaveAccessExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Biology.Levin.MixedSelectivityFieldControl as Mixed
import DASHI.Biology.Levin.MillerTravelingWaveAccessProducerExact as Miller

------------------------------------------------------------------------
-- Exact finite realization of the existing mixed-selectivity field-control
-- interface.  The same neuron/site and same stimulus have different effective
-- responses under two contexts because the context selects a moving field gate.
------------------------------------------------------------------------

waveMixedSelectivitySystem :
  Mixed.MixedSelectivitySystem
    Miller.Site2 Miller.Tick2 Bool Bool Miller.Tick2
waveMixedSelectivitySystem = record
  { Mixed.respond = λ neuron context stimulus →
      Miller.recruitedAt context neuron
  ; Mixed.fieldGate = λ pattern neuron →
      Miller.recruitedAt pattern neuron
  ; Mixed.contextPattern = λ context → context
  ; Mixed.sameStimulusMayChangeWithContext = true
  ; Mixed.gateActsOnPopulationNotSingleSynapse = true
  ; Mixed.fieldPatternDoesNotUniquelyDetermineResponse = true
  ; Mixed.interpretation =
      "same stored/input token, context-indexed traveling field, different effective participation"
  }

sameStimulusFirstContextResponse :
  Mixed.respond waveMixedSelectivitySystem
    Miller.leftSite Miller.firstTick false ≡ true
sameStimulusFirstContextResponse = refl

sameStimulusSecondContextResponse :
  Mixed.respond waveMixedSelectivitySystem
    Miller.leftSite Miller.secondTick false ≡ false
sameStimulusSecondContextResponse = refl

sameStimulusContextChangesParticipation :
  Mixed.respond waveMixedSelectivitySystem
    Miller.leftSite Miller.firstTick false
  ≡
  Mixed.respond waveMixedSelectivitySystem
    Miller.leftSite Miller.secondTick false → ⊥
sameStimulusContextChangesParticipation ()

canonicalContextDependentWitness :
  Mixed.ContextDependentWitness waveMixedSelectivitySystem
canonicalContextDependentWitness = record
  { Mixed.neuron = Miller.leftSite
  ; Mixed.first = Miller.firstTick
  ; Mixed.second = Miller.secondTick
  ; Mixed.stimulus = false
  ; Mixed.responsesDiffer = true
  }

record MixedSelectivityWaveBoundary : Set where
  constructor mixedSelectivityWaveBoundary
  field
    contextualResponseMeansArbitraryNeuron : Bool
    fieldGateMakesSynapsesIrrelevant : Bool
    mixedSelectivityImpliesConsciousness : Bool

canonicalMixedSelectivityWaveBoundary : MixedSelectivityWaveBoundary
canonicalMixedSelectivityWaveBoundary =
  mixedSelectivityWaveBoundary false false false
