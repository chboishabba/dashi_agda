module DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact where

------------------------------------------------------------------------
-- Q2 WELL-FOUNDED RECURSIVE STATE
--
-- A strict auxiliary formula inequality is not enough for termination if the
-- recursive transition rebuilds quotation/specialization payload around it.
--
-- This owner therefore puts the WHOLE recursive state under one Nat-valued
-- measure.  The state carries:
--
--   * current Cook formula;
--   * static program/self-code size;
--   * rebinding/specialization overhead;
--   * remaining resource budget.
--
-- The recursive measure charges the formula plus both persistent compiler
-- payloads.  A transition is admissible only when the measure of the actual
-- next state is strictly smaller than the current measure.
--
-- For any TOTAL next-step function returning Maybe State, strict decrease on
-- every successful next branch is enough to construct a finite termination
-- trace by Nat well-foundedness.
--
-- This is plumbing, not the P != NP breakthrough: the missing Q2 theorem must
-- show that the actual self-instantiation transition satisfies this strict
-- decrease condition.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (_<_; _≤_)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Product using (Σ; _,_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size

------------------------------------------------------------------------
-- Actual recursive state.
------------------------------------------------------------------------

record BoundedSelfReferenceState : Set where
  constructor bounded-self-reference-state
  field
    currentFormula : Cook.BooleanFormula

    -- Finite self-code/program payload retained across the recursive process.
    programCodeSize : Nat

    -- Cost of re-specializing/rebinding the program to the next formula.
    rebindingOverhead : Nat

    -- External accounting budget available at this state.
    resourceBudget : Nat

    -- The represented state must itself fit its declared budget.
    stateFitsBudget :
      Size.formulaNodeCount currentFormula
        + programCodeSize
        + rebindingOverhead
      ≤
      resourceBudget

open BoundedSelfReferenceState public

------------------------------------------------------------------------
-- Whole-state measure.
--
-- resourceBudget is an admissibility ceiling, not free decreasing fuel.  The
-- measure therefore charges the represented formula and persistent compiler
-- payload directly.
------------------------------------------------------------------------

recursiveMeasure : BoundedSelfReferenceState → Nat
recursiveMeasure state =
  Size.formulaNodeCount (currentFormula state)
  + programCodeSize state
  + rebindingOverhead state

------------------------------------------------------------------------
-- A total recursive step system.
------------------------------------------------------------------------

record BoundedSelfReferenceStepSystem : Set₁ where
  constructor bounded-self-reference-step-system
  field
    next :
      BoundedSelfReferenceState →
      Maybe BoundedSelfReferenceState

    nextStrictlyDecreases :
      (state nextState : BoundedSelfReferenceState) →
      next state ≡ just nextState →
      recursiveMeasure nextState
      <
      recursiveMeasure state

open BoundedSelfReferenceStepSystem public

------------------------------------------------------------------------
-- Finite execution trace.
------------------------------------------------------------------------

data TerminationTrace
    (system : BoundedSelfReferenceStepSystem) :
    BoundedSelfReferenceState →
    Set where

  stop :
    ∀ {state} →
    next system state ≡ nothing →
    TerminationTrace system state

  advance :
    ∀ {state nextState} →
    next system state ≡ just nextState →
    TerminationTrace system nextState →
    TerminationTrace system state

------------------------------------------------------------------------
-- Well-founded trace construction.
------------------------------------------------------------------------

buildTerminationTraceAcc :
  (system : BoundedSelfReferenceStepSystem) →
  (state : BoundedSelfReferenceState) →
  Acc _<_ (recursiveMeasure state) →
  TerminationTrace system state
buildTerminationTraceAcc
    system
    state
    (acc smaller)
    with next system state
... | nothing =
  stop refl
... | just nextState =
  advance
    refl
    (buildTerminationTraceAcc
      system
      nextState
      (smaller
        (nextStrictlyDecreases
          system
          state
          nextState
          refl)))

boundedSelfReferenceTerminates :
  (system : BoundedSelfReferenceStepSystem) →
  (initial : BoundedSelfReferenceState) →
  TerminationTrace system initial
boundedSelfReferenceTerminates system initial =
  buildTerminationTraceAcc
    system
    initial
    (<-wellFounded (recursiveMeasure initial))

------------------------------------------------------------------------
-- A trace contains an actual terminal state.
------------------------------------------------------------------------

traceTerminal :
  ∀ {system state} →
  TerminationTrace system state →
  Σ BoundedSelfReferenceState
    (λ terminalState →
      next system terminalState ≡ nothing)
traceTerminal (stop terminal) =
  _ , terminal
traceTerminal (advance step rest) =
  traceTerminal rest

boundedSelfReferenceHasTerminalState :
  (system : BoundedSelfReferenceStepSystem) →
  (initial : BoundedSelfReferenceState) →
  Σ BoundedSelfReferenceState
    (λ terminalState →
      next system terminalState ≡ nothing)
boundedSelfReferenceHasTerminalState system initial =
  traceTerminal
    (boundedSelfReferenceTerminates system initial)

------------------------------------------------------------------------
-- Q2 boundary.
--
-- This theorem proves the well-foundedness implication cleanly:
--
--   whole-state strict decrease
--      ->
--   finite recursive termination.
--
-- It does NOT prove that the self-diagonal transition decreases.  That missing
-- bridge must consume the Q1 all-overhead strict authority descent and show
-- that after quotation/rebinding the ACTUAL next state has smaller
-- recursiveMeasure.  Under the opposite-SAT body semantics, proving that bridge
-- is lower-bound-strength mathematics, exactly as the partial-Kleene
-- termination no-go theorem requires.
------------------------------------------------------------------------
