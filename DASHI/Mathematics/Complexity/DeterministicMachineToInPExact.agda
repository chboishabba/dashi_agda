module DASHI.Mathematics.Complexity.DeterministicMachineToInPExact where

------------------------------------------------------------------------
-- CLOCKED DETERMINISTIC EXECUTION -> LITERAL InP
--
-- The machine layer and the language/cost layer were previously adjacent but
-- not welded.  This owner uses the actual iterateDeterministic execution:
--
--   input
--     -> run for clock(inputLength input) steps
--     -> certified final configuration
--     -> Boolean output
--
-- and defines the accepted language by that exact output.  The only complexity
-- premise is an explicit realization saying this clocked evaluator is a
-- polynomial-time decider in the selected PolynomialCostModel.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Maybe.Base using (just)

import DASHI.Mathematics.Complexity.DeterministicNondeterministicMachineExact as Machine
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR

record ClockedDeterministicBooleanExecution
    (machine : Machine.DeterministicMachine) : Set₁ where
  field
    inputLength : Machine.dInput machine → Nat
    clock : Nat → Nat

    finalConfiguration :
      Machine.dInput machine →
      Machine.dConfiguration machine

    runExact :
      (input : Machine.dInput machine) →
      Machine.iterateDeterministic
        machine
        (clock (inputLength input))
        (Machine.dInitial machine input)
      ≡ just (finalConfiguration input)

    output :
      Machine.dConfiguration machine → Bool

open ClockedDeterministicBooleanExecution public

clockedDecision :
  ∀ {machine} →
  ClockedDeterministicBooleanExecution machine →
  Machine.dInput machine → Bool
clockedDecision execution input =
  output execution (finalConfiguration execution input)

clockedLanguage :
  ∀ {machine} →
  ClockedDeterministicBooleanExecution machine →
  PR.Language (Machine.dInput machine)
clockedLanguage execution = record
  { PR.accepts =
      λ input → clockedDecision execution input ≡ true
  }

record ClockedExecutionCostRealization
    {machine : Machine.DeterministicMachine}
    (cost : PR.PolynomialCostModel (Machine.dInput machine))
    (execution : ClockedDeterministicBooleanExecution machine) : Set₁ where
  field
    clockPolynomiallyBounded : Set
    exactEvaluatorPolynomial :
      PR.polynomialTimeDecider cost (clockedDecision execution)

open ClockedExecutionCostRealization public

clockedExecutionGivesInP :
  ∀ {machine}
    {cost : PR.PolynomialCostModel (Machine.dInput machine)}
    (execution : ClockedDeterministicBooleanExecution machine) →
  ClockedExecutionCostRealization cost execution →
  PR.InP cost (clockedLanguage execution)
clockedExecutionGivesInP execution realization = record
  { PR.decide = clockedDecision execution
  ; PR.sound = λ input accepted → accepted
  ; PR.complete = λ input accepted → accepted
  ; PR.polynomialDecision = exactEvaluatorPolynomial realization
  }

record DeterministicMachineToInPBoundary : Set where
  constructor deterministic-machine-to-inp-boundary
  field
    actualIterateDeterministicExecutionUsed : Bool
    literalLanguageDefinedFromExecution : Bool
    polynomialDecisionCostKeptExplicit : Bool
    genericFiniteMachineCostTheoremPaid : Bool

canonicalDeterministicMachineToInPBoundary :
  DeterministicMachineToInPBoundary
canonicalDeterministicMachineToInPBoundary =
  deterministic-machine-to-inp-boundary
    true true true false
