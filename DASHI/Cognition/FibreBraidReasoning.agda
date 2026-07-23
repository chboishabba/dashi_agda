module DASHI.Cognition.FibreBraidReasoning where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_)

import Base369 as Base
import DASHI.Cognition.IdEgoSuperego369 as Self

------------------------------------------------------------------------
-- Reasoning is represented as transport within and between fibres rather than
-- as a completed observer-of-observer chain.  A state retains latent, observed,
-- desired and compelled coordinates; auxiliary fibres can be braided into the
-- latent coordinate when they lower the global mismatch energy.
------------------------------------------------------------------------

record ReasoningState : Set where
  constructor reasoningState
  field
    latentValue    : Base.TriTruth
    observedValue  : Base.TriTruth
    desiredValue   : Base.TriTruth
    compelledValue : Base.TriTruth

open ReasoningState public

globalReasoningDefect : ReasoningState → Nat
globalReasoningDefect state =
  Self.triEqual (latentValue state) (desiredValue state) +
  Self.triEqual (observedValue state) (latentValue state) +
  Self.triEqual (desiredValue state) (compelledValue state)

pullAuxiliaryFibre : Base.TriTruth → ReasoningState → ReasoningState
pullAuxiliaryFibre auxiliary state = reasoningState
  (Base.triXor auxiliary (latentValue state))
  (observedValue state)
  (desiredValue state)
  (compelledValue state)

initialReasoningState : ReasoningState
initialReasoningState = reasoningState
  Base.tri-low
  Base.tri-mid
  Base.tri-high
  Base.tri-high

initialDefectIsTwo : globalReasoningDefect initialReasoningState ≡ 2
initialDefectIsTwo = refl

resolvedByHighAuxiliary : ReasoningState
resolvedByHighAuxiliary =
  pullAuxiliaryFibre Base.tri-high initialReasoningState

auxiliaryTransportLowersDefect :
  globalReasoningDefect resolvedByHighAuxiliary ≡ 1
auxiliaryTransportLowersDefect = refl

------------------------------------------------------------------------
-- Braid-wise transport: several auxiliary fibres act in sequence.  Base369's
-- proved associative triXor operation makes different parenthesisations of
-- the same ordered braid extensionally equal.
------------------------------------------------------------------------

transportBraid : List Base.TriTruth → Base.TriTruth → Base.TriTruth
transportBraid [] value = value
transportBraid (auxiliary ∷ rest) value =
  transportBraid rest (Base.triXor auxiliary value)

singleAuxiliaryTransport :
  transportBraid (Base.tri-high ∷ []) Base.tri-low ≡ Base.tri-high
singleAuxiliaryTransport = refl

record GoalDirectedFibreStep : Set where
  constructor goalDirectedFibreStep
  field
    before : ReasoningState
    auxiliary : Base.TriTruth
    after : ReasoningState
    afterIsTransport : after ≡ pullAuxiliaryFibre auxiliary before
    beforeDefect : Nat
    afterDefect  : Nat
    beforeDefectExact : beforeDefect ≡ globalReasoningDefect before
    afterDefectExact  : afterDefect ≡ globalReasoningDefect after

canonicalGoalDirectedStep : GoalDirectedFibreStep
canonicalGoalDirectedStep = goalDirectedFibreStep
  initialReasoningState
  Base.tri-high
  resolvedByHighAuxiliary
  refl
  2
  1
  refl
  refl
