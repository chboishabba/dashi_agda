module DASHI.Core.DashiMarkov where

open import DASHI.Core.Prelude

-- Lightweight core surface. The richer process-facing facade lives in
-- DASHI.Process.DASHIMarkovCompatibility.
--
-- A task-local DASHI state is the typed joined slice that still matters for
-- the next admissible transition.
record JoinedState
  (Carrier Residual Obligation Authority Boundary : Set) : Set where
  field
    carrier     : Carrier
    residual    : Residual
    obligations : Obligation
    authorities : Authority
    boundary    : Boundary

-- Structural update law. Probability is deliberately not primitive here.
record Transition (State Input : Set) : Set where
  field
    step : State → Input → State

-- Raw history may exist, but it must factor through the current DASHI state.
record Sufficiency
  (State Input History : Set)
  (transition : Transition State Input)
  : Set where
  field
    summarize : History → State
    append    : History → Input → History
    sufficient :
      (h : History) (x : Input) →
      summarize (append h x) ≡
      Transition.step transition (summarize h) x

record DASHIMarkov (State Input History : Set) : Set where
  field
    transition : Transition State Input
    sufficiency : Sufficiency State Input History transition

-- Optional compatibility projection for ordinary Markov-language consumers.
-- The kernel is relation-valued rather than probability-valued so finite
-- chains, HMMs, MDPs, and deterministic lanes can all share the same surface.
record MarkovCompatibility
  (State Input Observation : Set)
  (transition : Transition State Input)
  : Set₁ where
  field
    kernel   : State → Input → State → Set
    emit     : State → Observation → Set
    realizes :
      (s : State) (x : Input) (s' : State) →
      kernel s x s' → s' ≡ Transition.step transition s x

-- Non-promotion status: this module only names the compatibility layer.
data DASHIMarkovStatus : Set where
  compatibilitySurfaceOnlyNoPromotion : DASHIMarkovStatus
