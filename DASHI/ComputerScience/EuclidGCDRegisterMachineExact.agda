module DASHI.ComputerScience.EuclidGCDRegisterMachineExact where

open import DASHI.Core.Prelude
open import Data.Nat.GCD using (gcd)

import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.ComputerScience.FibreProgramComplexityExact as Complexity

------------------------------------------------------------------------
-- SUBTRACTIVE EUCLID ON THE RADIX-NEUTRAL TINY MACHINE
--
-- Mathematical specification remains Data.Nat.GCD.gcd.  This module provides
-- one concrete machine implementation and an exact 48,18 regression.
--
-- 0: JEQ r0 r1 6
-- 1: JLT r0 r1 4
-- 2: SUB r0 r1
-- 3: JMP 0
-- 4: SUB r1 r0
-- 5: JMP 0
-- 6: OUT r0
-- 7: HALT
------------------------------------------------------------------------

euclidProgram : Machine.Program
euclidProgram =
  Machine.jumpIfEqual Machine.r0 Machine.r1 6
  ∷ Machine.jumpIfLess Machine.r0 Machine.r1 4
  ∷ Machine.subRegister Machine.r0 Machine.r1
  ∷ Machine.jump 0
  ∷ Machine.subRegister Machine.r1 Machine.r0
  ∷ Machine.jump 0
  ∷ Machine.outputRegister Machine.r0
  ∷ Machine.halt
  ∷ []

euclidInitialState : Nat → Nat → Machine.MachineState
euclidInitialState a b =
  Machine.machineState
    0
    euclidProgram
    []
    (Machine.registerFile a b 0)
    []
    false
    0

-- Exact fuel for the canonical 48,18 fixture.
euclid4818Fuel : Nat
euclid4818Fuel = 19

euclid4818Final : Machine.MachineState
euclid4818Final =
  Machine.runFuel euclid4818Fuel (euclidInitialState 48 18)

euclid4818Output : Machine.output euclid4818Final ≡ 6 ∷ []
euclid4818Output = refl

euclid4818Halts : Machine.halted euclid4818Final ≡ true
euclid4818Halts = refl

euclid4818Cycles : Machine.cycles euclid4818Final ≡ 19
euclid4818Cycles = refl

euclid4818TerminalPC : Machine.pc euclid4818Final ≡ 7
euclid4818TerminalPC = refl

euclid4818TerminalR0 :
  Machine.reg0 (Machine.registers euclid4818Final) ≡ 6
euclid4818TerminalR0 = refl

euclid4818TerminalR1 :
  Machine.reg1 (Machine.registers euclid4818Final) ≡ 6
euclid4818TerminalR1 = refl

libraryGcd4818IsSix : gcd 48 18 ≡ 6
libraryGcd4818IsSix = refl

machineResultMatchesLibraryGcd4818 :
  Machine.reg0 (Machine.registers euclid4818Final) ≡ gcd 48 18
machineResultMatchesLibraryGcd4818 = refl

------------------------------------------------------------------------
-- Actual execution path and consumer-indexed costs.
------------------------------------------------------------------------

traceFuel : Nat → Machine.MachineState → List Machine.MachineState
traceFuel zero state = state ∷ []
traceFuel (suc fuel) state = state ∷ traceFuel fuel (Machine.step state)

euclid4818Path : Complexity.ExecutionFibrePath Machine.MachineState
euclid4818Path =
  Complexity.executionFibrePath
    (traceFuel euclid4818Fuel (euclidInitialState 48 18))

euclid4818StateVisits :
  Complexity.K Complexity.stateVisitConsumer euclid4818Path ≡ 20
euclid4818StateVisits = refl

euclid4818Transitions :
  Complexity.K Complexity.transitionConsumer euclid4818Path ≡ 19
euclid4818Transitions = refl

euclid4818HeadTravel :
  Complexity.K (Complexity.headTravelConsumer Machine.pc) euclid4818Path ≡ 35
euclid4818HeadTravel = refl

euclid4818HeadTravelDiffersFromTransitions :
  Complexity.K (Complexity.headTravelConsumer Machine.pc) euclid4818Path
  ≡ Complexity.K Complexity.transitionConsumer euclid4818Path →
  ⊥
euclid4818HeadTravelDiffersFromTransitions ()

record EuclidGCDMachineReceipt : Set where
  constructor euclidGCDMachineReceipt
  field
    inputA : Nat
    inputB : Nat
    machineResult : Nat
    mathematicalResult : Nat
    outputTape : List Nat
    executionCycles : Nat
    stateVisits : Nat
    headTravel : Nat
    machineResultExact : machineResult ≡ 6
    mathematicalResultExact : mathematicalResult ≡ 6
    implementationMatchesSpecification : machineResult ≡ mathematicalResult
    outputExact : outputTape ≡ 6 ∷ []
    cyclesExact : executionCycles ≡ 19
    visitsExact : stateVisits ≡ 20
    headTravelExact : headTravel ≡ 35

canonicalEuclid4818Receipt : EuclidGCDMachineReceipt
canonicalEuclid4818Receipt =
  euclidGCDMachineReceipt
    48
    18
    (Machine.reg0 (Machine.registers euclid4818Final))
    (gcd 48 18)
    (Machine.output euclid4818Final)
    (Machine.cycles euclid4818Final)
    (Complexity.K Complexity.stateVisitConsumer euclid4818Path)
    (Complexity.K (Complexity.headTravelConsumer Machine.pc) euclid4818Path)
    refl refl refl refl refl refl refl

record EuclidGCDBoundary : Set where
  constructor euclidGCDBoundary
  field
    mathematicalGcdRedefinedHere : Bool
    machineImplementationDistinctFromSpecification : Bool
    concrete4818CorrectnessClosed : Bool
    concrete4818TerminationClosed : Bool
    concrete4818PathCostsClosed : Bool
    genericAllInputCorrectnessClosed : Bool
    asymptoticComplexityClosed : Bool
    radixFixedAtMachineSemantics : Bool

canonicalEuclidGCDBoundary : EuclidGCDBoundary
canonicalEuclidGCDBoundary =
  euclidGCDBoundary
    false true true true true false false false
