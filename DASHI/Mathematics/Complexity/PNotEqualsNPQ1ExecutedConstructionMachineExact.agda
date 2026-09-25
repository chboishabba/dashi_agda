module DASHI.Mathematics.Complexity.PNotEqualsNPQ1ExecutedConstructionMachineExact where

------------------------------------------------------------------------
-- Q1 CONSTRUCTION: REPLACE AUXILIARY UNIT TRACE BY MACHINE EXECUTION
--
-- Existing owner:
--   PNotEqualsNPQ1OperationalConstructionCostExact
--
-- charges:
--
--   graphCellCount + length auxiliaryTrace.
--
-- The auxiliary trace there is deliberately weak: List Unit accounts for a
-- number of steps but does not prove that those steps execute a machine which
-- actually constructs the returned Q1 witness.
--
-- This owner introduces the strict successor receipt:
--
--   deterministic step function
--   + start/final machine states
--   + exact n-step execution
--   + decoder
--   + proof that the final state decodes to THE SAME Q1 witness
--   + graphCells + n + measure(next) < measure(current).
--
-- It then compiles this stronger receipt back to the existing operational
-- interface.  Hence all downstream Q2 recurrence machinery can be reused
-- unchanged while new constructors can stop using an untyped List Unit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.ComputerScience.FibreProgramComplexityExact as Complexity
import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPBoundedSelfReferenceWellFoundedExact as Q2
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ConstructionChargedRecurrenceExact as Charged
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1OperationalConstructionCostExact as Operational
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1ReachableStateRecurrenceExact as Recurrence
import DASHI.Mathematics.Complexity.PNotEqualsNPRestrictionQuotientClassSelectionAlgorithmExact as Selection
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPResourceClosingRestrictionQuotientExact as Quotient
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge

------------------------------------------------------------------------
-- Exact deterministic n-step execution.
------------------------------------------------------------------------

data Iterates
    {MachineState : Set}
    (step : MachineState → MachineState) :
    Nat → MachineState → MachineState → Set where

  iteratesZero :
    ∀ {state} →
    Iterates step zero state state

  iteratesStep :
    ∀ {steps start final} →
    Iterates step steps (step start) final →
    Iterates step (suc steps) start final

------------------------------------------------------------------------
-- Strict replacement for OperationalQ1ConstructionRun.
------------------------------------------------------------------------

record ExecutedQ1ConstructionRun
    (state : Q2.BoundedSelfReferenceState) : Set₁ where
  constructor executed-q1-construction-run
  field
    MachineState : Set

    machineStep :
      MachineState → MachineState

    decodeWitness :
      MachineState →
      Maybe (Recurrence.Q1StateWitness state)

    machineStart machineFinal :
      MachineState

    machineStepCount :
      Nat

    machineExecution :
      Iterates
        machineStep
        machineStepCount
        machineStart
        machineFinal

    q1Witness :
      Recurrence.Q1StateWitness state

    machineFinalDecodesExactWitness :
      decodeWitness machineFinal
      ≡
      just q1Witness

    machineConstructionAndNextStrict :
      (Operational.q1WitnessGraphCellCount q1Witness
        + machineStepCount)
      +
      Q2.recursiveMeasure
        (Charged.q1WitnessNextState state q1Witness)
      <
      Q2.recursiveMeasure state

open ExecutedQ1ConstructionRun public

------------------------------------------------------------------------
-- Unit-list compatibility is now derived from the machine step count.
------------------------------------------------------------------------

unitTrace : Nat → List ⊤
unitTrace zero =
  []
unitTrace (suc steps) =
  tt ∷ unitTrace steps

unitTraceLengthExact :
  (steps : Nat) →
  length (unitTrace steps) ≡ steps
unitTraceLengthExact zero =
  refl
unitTraceLengthExact (suc steps)
    rewrite unitTraceLengthExact steps =
  refl

------------------------------------------------------------------------
-- Compile the strict receipt back to the old operational interface.
--
-- The false/true emitted rows are definitionally the actual quotient step
-- table.  No independent row target is supplied by the stronger constructor.
------------------------------------------------------------------------

executedRunToOperationalRun :
  ∀ {state : Q2.BoundedSelfReferenceState} →
  ExecutedQ1ConstructionRun state →
  Operational.OperationalQ1ConstructionRun state
executedRunToOperationalRun {state} run =
  record
    { Operational.q1Witness =
        q1Witness run

    ; Operational.emittedFalseTarget =
        λ stateIndex →
          Quotient.step
            (Operational.q1WitnessQuotient (q1Witness run))
            stateIndex
            false

    ; Operational.emittedTrueTarget =
        λ stateIndex →
          Quotient.step
            (Operational.q1WitnessQuotient (q1Witness run))
            stateIndex
            true

    ; Operational.emittedFalseTargetExact =
        λ stateIndex → refl

    ; Operational.emittedTrueTargetExact =
        λ stateIndex → refl

    ; Operational.auxiliaryTrace =
        unitTrace (machineStepCount run)

    ; Operational.operationalAndNextStrict =
        operationalStrict
    }
  where
    operationalStrict :
      (Operational.q1WitnessGraphCellCount (q1Witness run)
        + length (unitTrace (machineStepCount run)))
      +
      Q2.recursiveMeasure
        (Charged.q1WitnessNextState state (q1Witness run))
      <
      Q2.recursiveMeasure state
    operationalStrict
      rewrite unitTraceLengthExact (machineStepCount run) =
      machineConstructionAndNextStrict run

------------------------------------------------------------------------
-- Live constructor and Q2 compiler.
------------------------------------------------------------------------

ExecutedQ1StateConstructor : Set₁
ExecutedQ1StateConstructor =
  (state : Q2.BoundedSelfReferenceState) →
  Maybe (ExecutedQ1ConstructionRun state)

executedConstructorToOperational :
  ExecutedQ1StateConstructor →
  Operational.OperationalQ1StateConstructor
executedConstructorToOperational constructor state
    with constructor state
... | nothing =
  nothing
... | just run =
  just (executedRunToOperationalRun run)

executedConstructorToQ2StepSystem :
  ExecutedQ1StateConstructor →
  Q2.BoundedSelfReferenceStepSystem
executedConstructorToQ2StepSystem constructor =
  Operational.operationalConstructorToQ2StepSystem
    (executedConstructorToOperational constructor)

------------------------------------------------------------------------
-- Machine execution cost inherits the existing strict resource consequence.
------------------------------------------------------------------------

machineStepCountStrictlyBelowCurrentMeasure :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : ExecutedQ1ConstructionRun state) →
  machineStepCount run
  <
  Q2.recursiveMeasure state
machineStepCountStrictlyBelowCurrentMeasure {state} run =
  NatP.≤-<-trans
    machineStepsBelowChargedLeft
    (machineConstructionAndNextStrict run)
  where
    machineStepsBelowGraphPlusSteps :
      machineStepCount run
      ≤
      Operational.q1WitnessGraphCellCount (q1Witness run)
        + machineStepCount run
    machineStepsBelowGraphPlusSteps =
      NatP.m≤n+m
        (machineStepCount run)
        (Operational.q1WitnessGraphCellCount (q1Witness run))

    machineStepsBelowChargedLeft :
      machineStepCount run
      ≤
      (Operational.q1WitnessGraphCellCount (q1Witness run)
        + machineStepCount run)
      +
      Q2.recursiveMeasure
        (Charged.q1WitnessNextState state (q1Witness run))
    machineStepsBelowChargedLeft =
      NatP.≤-trans
        machineStepsBelowGraphPlusSteps
        (NatP.m≤m+n
          (Operational.q1WitnessGraphCellCount (q1Witness run)
            + machineStepCount run)
          (Q2.recursiveMeasure
            (Charged.q1WitnessNextState state (q1Witness run))))

------------------------------------------------------------------------
-- Existing executable reachable-class selector is immediately available once
-- the machine has produced the exact Q1 witness.
------------------------------------------------------------------------

selectedReachableClass :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : ExecutedQ1ConstructionRun state)
    {currentVariables : Nat}
    {current : SAT.BooleanFormula currentVariables} →
  Family.RestrictionDerivation
    (Bridge.cookToIndexed (Q2.currentFormula state))
    current →
  Fin
    (Operational.q1WitnessStateCount
      (q1Witness run))
selectedReachableClass run derivation =
  Selection.selectClass
    (Operational.q1WitnessQuotient (q1Witness run))
    derivation

selectedReachableClassExact :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : ExecutedQ1ConstructionRun state)
    {currentVariables : Nat}
    {current : SAT.BooleanFormula currentVariables}
    (derivation :
      Family.RestrictionDerivation
        (Bridge.cookToIndexed (Q2.currentFormula state))
        current) →
  selectedReachableClass run derivation
  ≡
  Quotient.classify
    (Operational.q1WitnessQuotient (q1Witness run))
    derivation
selectedReachableClassExact run derivation =
  Selection.selectClassExact
    (Operational.q1WitnessQuotient (q1Witness run))
    derivation

selectedReachableClassPath :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : ExecutedQ1ConstructionRun state)
    {currentVariables : Nat}
    {current : SAT.BooleanFormula currentVariables} →
  Family.RestrictionDerivation
    (Bridge.cookToIndexed (Q2.currentFormula state))
    current →
  Complexity.ExecutionFibrePath
    (Fin
      (Operational.q1WitnessStateCount
        (q1Witness run)))
selectedReachableClassPath run derivation =
  Selection.selectionPath
    (Operational.q1WitnessQuotient (q1Witness run))
    derivation

selectedReachableClassCostExact :
  ∀ {state : Q2.BoundedSelfReferenceState}
    (run : ExecutedQ1ConstructionRun state)
    {currentVariables : Nat}
    {current : SAT.BooleanFormula currentVariables}
    (derivation :
      Family.RestrictionDerivation
        (Bridge.cookToIndexed (Q2.currentFormula state))
        current) →
  Complexity.K
    Complexity.transitionConsumer
    (selectedReachableClassPath run derivation)
  ≡
  Selection.restrictionDepth derivation
selectedReachableClassCostExact run derivation =
  Selection.selectionTransitionCostExact
    (Operational.q1WitnessQuotient (q1Witness run))
    derivation

------------------------------------------------------------------------
-- REPLACEMENT STATUS
--
-- PAID:
--
--   List Unit auxiliary accounting
--      ->
--   exact deterministic execution:
--     step/start/final/n-step trace
--     + final-state decoder
--     + decoder returns the SAME Q1 witness
--     + charged strict descent.
--
--   Once that witness exists, reachable class selection is an already-existing
--   executable algorithm with exact transition cost = restriction depth.
--
-- STILL OPEN:
--
--   instantiate ExecutedQ1StateConstructor with the actual quotient /
--   representative-chain construction algorithm.
--
-- In particular the new machine interface prevents an unrelated cheap trace
-- from paying for an expensive omniscient constructor: the final machine state
-- must decode to the exact closed-Q1 witness consumed by Q2.
------------------------------------------------------------------------
