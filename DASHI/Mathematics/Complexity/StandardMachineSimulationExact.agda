module DASHI.Mathematics.Complexity.StandardMachineSimulationExact where

------------------------------------------------------------------------
-- EXACT SIMULATION / PHASE COMPOSITION FOR CONVENTIONAL STANDARD TMs
--
-- A compiler proof needs to show that a target finite machine actually runs a
-- source machine, not merely that their final Boolean answers happen to agree.
-- This owner provides the minimal reusable relation:
--
--   configuration embedding + one-step preservation
--      -> exact T-step run preservation.
--
-- Exact target-machine runs also concatenate with additive step clocks.  No
-- complexity claim, SAT semantics or self-reference is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Maybe.Base using (just)

import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as Standard
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as Run

------------------------------------------------------------------------
-- Step-preserving embedding.
------------------------------------------------------------------------

record StandardMachineSimulation
    {SourceState SourceSymbol TargetState TargetSymbol : Set}
    (source : Standard.StandardSingleTapeMachine SourceState SourceSymbol)
    (target : Standard.StandardSingleTapeMachine TargetState TargetSymbol) : Set₁ where
  field
    embed :
      Standard.StandardConfiguration source →
      Standard.StandardConfiguration target

    stepExact :
      ∀ {before after} →
      Standard.standardNext source before ≡ just after →
      Standard.standardNext target (embed before) ≡ just (embed after)

open StandardMachineSimulation public

------------------------------------------------------------------------
-- Exact run preservation; there is no simulation clock blow-up at this layer.
------------------------------------------------------------------------

simulateExactRun :
  ∀ {SourceState SourceSymbol TargetState TargetSymbol : Set}
    {source : Standard.StandardSingleTapeMachine SourceState SourceSymbol}
    {target : Standard.StandardSingleTapeMachine TargetState TargetSymbol}
    (simulation : StandardMachineSimulation source target)
    {steps : Nat}
    {start finish : Standard.StandardConfiguration source} →
  Run.StandardExactRun source steps start finish →
  Run.StandardExactRun target steps
    (embed simulation start)
    (embed simulation finish)
simulateExactRun simulation Run.standardRunDone =
  Run.standardRunDone
simulateExactRun simulation (Run.standardRunStep edge rest) =
  Run.standardRunStep
    (stepExact simulation edge)
    (simulateExactRun simulation rest)

------------------------------------------------------------------------
-- Sequential phase composition on one target machine.
------------------------------------------------------------------------

appendExactRuns :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {leftSteps rightSteps : Nat}
    {start middle finish : Standard.StandardConfiguration machine} →
  Run.StandardExactRun machine leftSteps start middle →
  Run.StandardExactRun machine rightSteps middle finish →
  Run.StandardExactRun machine (leftSteps + rightSteps) start finish
appendExactRuns Run.standardRunDone right =
  right
appendExactRuns (Run.standardRunStep edge rest) right =
  Run.standardRunStep edge (appendExactRuns rest right)

appendThreeExactRuns :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {firstSteps middleSteps lastSteps : Nat}
    {start firstEnd middleEnd finish : Standard.StandardConfiguration machine} →
  Run.StandardExactRun machine firstSteps start firstEnd →
  Run.StandardExactRun machine middleSteps firstEnd middleEnd →
  Run.StandardExactRun machine lastSteps middleEnd finish →
  Run.StandardExactRun machine
    ((firstSteps + middleSteps) + lastSteps)
    start finish
appendThreeExactRuns first middle last =
  appendExactRuns
    (appendExactRuns first middle)
    last

------------------------------------------------------------------------
-- Step-index transport for an externally proved exact accounting equation.
------------------------------------------------------------------------

transportRunSteps :
  ∀ {State Symbol : Set}
    {machine : Standard.StandardSingleTapeMachine State Symbol}
    {left right : Nat}
    {start finish : Standard.StandardConfiguration machine} →
  left ≡ right →
  Run.StandardExactRun machine left start finish →
  Run.StandardExactRun machine right start finish
transportRunSteps refl run = run

------------------------------------------------------------------------
-- FRONTIER
--
-- Downstream compiler proofs can now expose a real phase decomposition:
--
--   prefix ; simulated source run ; suffix
--
-- with the source run mapped edge-for-edge into the target and exact additive
-- time accounting.  Any stronger statement that a compiled machine "calls D"
-- should consume this owner rather than use a bare output equality.
------------------------------------------------------------------------
