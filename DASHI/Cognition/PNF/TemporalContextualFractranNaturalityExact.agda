module DASHI.Cognition.PNF.TemporalContextualFractranNaturalityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Cognition.PNF.BracketedTSFVFractranWorldFibreExact as World

------------------------------------------------------------------------
-- Time-indexed contextual fibres.  Same coarse state at two times does not
-- identify histories.  Symmetry/phase inversion commuting with time transport
-- is a theorem obligation, not a consequence of carrier geometry.
------------------------------------------------------------------------

data TimeIndex : Set where
  time : Nat → TimeIndex

record TemporalOccurrenceState : Set where
  constructor temporalOccurrenceState
  field
    atTime : TimeIndex
    world : World.WorldHistory
    occurrenceState : Context.ContextualOccurrenceState

open TemporalOccurrenceState public

record TemporalTransport : Set₁ where
  constructor temporalTransport
  field
    transport : TemporalOccurrenceState → TemporalOccurrenceState
    preservesWorldIdentity :
      (state : TemporalOccurrenceState) →
      World.worldId (TemporalOccurrenceState.world (transport state))
      ≡ World.worldId (TemporalOccurrenceState.world state)

open TemporalTransport public

record TemporalPhaseNaturality
  (T : TemporalTransport)
  : Set₁ where
  constructor temporalPhaseNaturality
  field
    phaseAction : TemporalOccurrenceState → TemporalOccurrenceState
    commutes :
      (state : TemporalOccurrenceState) →
      transport T (phaseAction state)
      ≡ phaseAction (transport T state)

open TemporalPhaseNaturality public

record TemporalSymmetryDefect
  (T : TemporalTransport)
  : Set₁ where
  constructor temporalSymmetryDefect
  field
    phaseAction : TemporalOccurrenceState → TemporalOccurrenceState
    witnessState : TemporalOccurrenceState
    orderMatters :
      transport T (phaseAction witnessState)
      ≡ phaseAction (transport T witnessState)
      → Bool

record TemporalContextualBoundary : Set where
  constructor temporalContextualBoundary
  field
    sameCoarseStateMeansSameHistory : Bool
    phaseNaturalityIsAutomatic : Bool
    temporalTransportMayChangeBracketExposure : Bool
    differentHistoriesMayShareCurrentZero : Bool

canonicalTemporalContextualBoundary : TemporalContextualBoundary
canonicalTemporalContextualBoundary =
  temporalContextualBoundary false false true true
