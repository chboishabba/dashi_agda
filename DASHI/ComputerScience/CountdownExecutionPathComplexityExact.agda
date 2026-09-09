module DASHI.ComputerScience.CountdownExecutionPathComplexityExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.ComputerScience.FibreProgramComplexityExact as Complexity

------------------------------------------------------------------------
-- FIRST LOOPING EXECUTION FIBRE
------------------------------------------------------------------------

traceFuel : Nat → Machine.MachineState → List Machine.MachineState
traceFuel zero state = state ∷ []
traceFuel (suc fuel) state = state ∷ traceFuel fuel (Machine.step state)

countdownPath : Nat → Complexity.ExecutionFibrePath Machine.MachineState
countdownPath n =
  Complexity.executionFibrePath
    (traceFuel (Machine.countdownFuel n) (Machine.countdownInitialState n))

countdownThreePath : Complexity.ExecutionFibrePath Machine.MachineState
countdownThreePath = countdownPath 3

countdownThreeStateVisits :
  Complexity.K Complexity.stateVisitConsumer countdownThreePath ≡ 15
countdownThreeStateVisits = refl

countdownThreeTransitions :
  Complexity.K Complexity.transitionConsumer countdownThreePath ≡ 14
countdownThreeTransitions = refl

countdownThreeHeadTravel :
  Complexity.K (Complexity.headTravelConsumer Machine.pc) countdownThreePath ≡ 22
countdownThreeHeadTravel = refl

------------------------------------------------------------------------
-- Execution cost formula used by the machine fixture.
--
-- A positive countdown iteration performs JZ, OUT, SUB, JMP = four steps.
-- Termination performs final JZ and HALT = two steps.  The generic semantic
-- induction over arbitrary n remains a separate theorem obligation; these
-- exact fixtures ensure the path consumer agrees with the machine execution.
------------------------------------------------------------------------

countdownCostFormula : Nat → Nat
countdownCostFormula n = 4 * n + 2

countdownCostFormulaZero : countdownCostFormula 0 ≡ 2
countdownCostFormulaZero = refl

countdownCostFormulaOne : countdownCostFormula 1 ≡ 6
countdownCostFormulaOne = refl

countdownCostFormulaThree : countdownCostFormula 3 ≡ 14
countdownCostFormulaThree = refl

countdownThreePathCostMatchesMachineCycles :
  Complexity.K Complexity.transitionConsumer countdownThreePath
  ≡ Machine.cycles (Machine.countdownFinal 3)
countdownThreePathCostMatchesMachineCycles = refl

countdownThreePathHeadTravelDiffersFromTransitions :
  Complexity.K (Complexity.headTravelConsumer Machine.pc) countdownThreePath
  ≡ Complexity.K Complexity.transitionConsumer countdownThreePath →
  ⊥
countdownThreePathHeadTravelDiffersFromTransitions ()

record CountdownPathComplexityReceipt : Set where
  constructor countdownPathComplexityReceipt
  field
    input : Nat
    stateVisits : Nat
    transitions : Nat
    headTravel : Nat
    output : List Nat
    halted : Bool
    stateVisitsExact : stateVisits ≡ 15
    transitionsExact : transitions ≡ 14
    headTravelExact : headTravel ≡ 22
    outputExact : output ≡ 3 ∷ 2 ∷ 1 ∷ []
    haltedExact : halted ≡ true

canonicalCountdownThreePathComplexityReceipt : CountdownPathComplexityReceipt
canonicalCountdownThreePathComplexityReceipt =
  countdownPathComplexityReceipt
    3
    (Complexity.K Complexity.stateVisitConsumer countdownThreePath)
    (Complexity.K Complexity.transitionConsumer countdownThreePath)
    (Complexity.K (Complexity.headTravelConsumer Machine.pc) countdownThreePath)
    (Machine.output (Machine.countdownFinal 3))
    (Machine.halted (Machine.countdownFinal 3))
    refl refl refl refl refl

record CountdownComplexityBoundary : Set where
  constructor countdownComplexityBoundary
  field
    straightLineExecutionOnly : Bool
    branchAndLoopExecutionPresent : Bool
    transitionAndHeadTravelCollapsed : Bool
    exactInputThreePathClosed : Bool
    genericAllInputCostInductionClosed : Bool

canonicalCountdownComplexityBoundary : CountdownComplexityBoundary
canonicalCountdownComplexityBoundary =
  countdownComplexityBoundary false true false true false
