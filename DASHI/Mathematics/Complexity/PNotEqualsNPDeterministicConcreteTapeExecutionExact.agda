module DASHI.Mathematics.Complexity.PNotEqualsNPDeterministicConcreteTapeExecutionExact where

------------------------------------------------------------------------
-- DETERMINISTIC REFINEMENT OF THE RELATIONAL CONCRETE TAPE MACHINE
--
-- ConcreteTapeMachineLocalityExact intentionally exposes MachineStep as a
-- proof-relevant relation.  The remaining semantic-quotation frontier needs
-- an executable candidate/interpreter, so it cannot stop at existential
-- accepting runs.
--
-- This owner adds the minimal deterministic execution layer WITHOUT changing
-- the underlying machine semantics:
--
--   next : TapeRow -> Maybe TapeRow
--
-- together with a proof that every returned successor is a literal existing
-- WellFormedMachineStep of the same ConcreteTapeMachine.
--
-- An n-step deterministic execution compiles to the repository's canonical
-- WellFormedTapeRun and, with exact initial/accepting endpoint receipts, to the
-- exact-budget accepting-run object consumed by concrete Cook--Levin.
--
-- No SAT predicate or decision oracle occurs in this owner.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Maybe.Base using (Maybe; just; nothing)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.ConcreteTapeWellFormedConfigurationExact as WF
import DASHI.Mathematics.Complexity.ConcreteTapeRunCNFWeldExact as Run
import DASHI.Mathematics.Complexity.ConcreteTapeAcceptingRunCNFExact as Accepting
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeTimeBudgetPaddingExact as Guard
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinExactBudgetIff as Exact

------------------------------------------------------------------------
-- A deterministic successor is admitted only by local-machine soundness.
------------------------------------------------------------------------

record DeterministicTapeSuccessor
    (machine : Local.ConcreteTapeMachine) : Set₁ where
  field
    next :
      Local.TapeRow machine →
      Maybe (Local.TapeRow machine)

    nextSound :
      (before after : Local.TapeRow machine) →
      next before ≡ just after →
      WF.WellFormedMachineStep machine before after

open DeterministicTapeSuccessor public

------------------------------------------------------------------------
-- Exact deterministic execution trace.
------------------------------------------------------------------------

data DeterministicExecution
    {machine : Local.ConcreteTapeMachine}
    (successor : DeterministicTapeSuccessor machine) :
    Nat →
    Local.TapeRow machine →
    Local.TapeRow machine →
    Set₁ where

  executionDone :
    ∀ {row} →
    DeterministicExecution successor zero row row

  executionStep :
    ∀ {steps current nextRow finish} →
    next successor current ≡ just nextRow →
    DeterministicExecution successor steps nextRow finish →
    DeterministicExecution successor (suc steps) current finish

------------------------------------------------------------------------
-- The visited-row list is executable from the proof-relevant trace.
------------------------------------------------------------------------

executionRows :
  ∀ {machine : Local.ConcreteTapeMachine}
    {successor : DeterministicTapeSuccessor machine}
    {steps : Nat}
    {start finish : Local.TapeRow machine} →
  DeterministicExecution successor steps start finish →
  List (Local.TapeRow machine)
executionRows executionDone =
  []
executionRows (executionStep {nextRow = nextRow} nextExact rest) =
  nextRow ∷ executionRows rest

------------------------------------------------------------------------
-- Deterministic execution is a canonical repository WellFormedTapeRun.
------------------------------------------------------------------------

executionToWellFormedRun :
  ∀ {machine : Local.ConcreteTapeMachine}
    {successor : DeterministicTapeSuccessor machine}
    {steps : Nat}
    {start finish : Local.TapeRow machine}
    (execution : DeterministicExecution successor steps start finish) →
  Run.WellFormedTapeRun
    machine
    start
    (executionRows execution)
    finish
executionToWellFormedRun executionDone =
  Run.runDone
executionToWellFormedRun
    {successor = successor}
    (executionStep {current = current} {nextRow = nextRow}
      nextExact rest) =
  Run.runStep
    (nextSound successor current nextRow nextExact)
    (executionToWellFormedRun rest)

executionRunLengthExact :
  ∀ {machine : Local.ConcreteTapeMachine}
    {successor : DeterministicTapeSuccessor machine}
    {steps : Nat}
    {start finish : Local.TapeRow machine}
    (execution : DeterministicExecution successor steps start finish) →
  Run.runLength (executionToWellFormedRun execution)
  ≡ steps
executionRunLengthExact executionDone =
  refl
executionRunLengthExact (executionStep nextExact rest)
    rewrite executionRunLengthExact rest =
  refl

------------------------------------------------------------------------
-- Exact-budget accepting run compiler.
------------------------------------------------------------------------

deterministicExecutionToExactBudgetAcceptingRun :
  ∀ {machine : Local.ConcreteTapeMachine}
    {successor : DeterministicTapeSuccessor machine}
    (input : Input.InputWord machine)
    (steps : Nat)
    {finish : Local.TapeRow machine}
    (execution :
      DeterministicExecution
        successor
        steps
        (Guard.guardedInitialRow input steps)
        finish) →
    Accepting.InitialInteriorRow
      machine
      (Guard.guardedInitialRow input steps) →
    Accepting.AcceptingInteriorRow machine finish →
  Exact.ExactBudgetAcceptingRun input steps
deterministicExecutionToExactBudgetAcceptingRun
    input steps {finish} execution initial accepting =
  record
    { Exact.rows = executionRows execution
    ; Exact.finish = finish
    ; Exact.certificate = record
        { Accepting.initial = initial
        ; Accepting.run = executionToWellFormedRun execution
        ; Accepting.accepting = accepting
        }
    ; Exact.exactLength = executionRunLengthExact execution
    }

------------------------------------------------------------------------
-- Converse uniqueness boundary.
--
-- A relational accepting run is not automatically the deterministic run:
-- machines may have multiple locally legal rules.  Promotion therefore needs
-- an explicit theorem that each relational edge agrees with `next`.
------------------------------------------------------------------------

record DeterministicRefinementComplete
    (machine : Local.ConcreteTapeMachine)
    (successor : DeterministicTapeSuccessor machine) : Set₁ where
  field
    everyWellFormedStepSelected :
      ∀ {before after} →
      WF.WellFormedMachineStep machine before after →
      next successor before ≡ just after

open DeterministicRefinementComplete public

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The concrete semantic-quotation target can now be split honestly:
--
--   1. construct a literal ConcreteTapeMachine;
--   2. construct a deterministic successor whose every step is locally sound;
--   3. prove completeness/uniqueness where SAT -> abstract-run recovery needs
--      to identify arbitrary accepting runs with the deterministic execution;
--   4. bind candidate code and opposite-interpreter execution to that SAME
--      deterministic machine.
--
-- The remaining hard object is the candidate/interpreter compiler, not the
-- Cook--Levin accepting-run transport.
------------------------------------------------------------------------
