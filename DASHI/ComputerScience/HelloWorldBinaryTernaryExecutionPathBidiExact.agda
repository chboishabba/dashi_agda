module DASHI.ComputerScience.HelloWorldBinaryTernaryExecutionPathBidiExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.HelloWorldEncodedWordMachineExact as Machine
import DASHI.ComputerScience.HelloWorldBinaryTernaryFramedWordStorageExact as Storage
import DASHI.ComputerScience.FibreProgramComplexityExact as Complexity

------------------------------------------------------------------------
-- BINARY / TERNARY-27 EXECUTION BIDI
--
-- The two storage fibres are decoded before entering the canonical numeric
-- machine.  They therefore do not define two machine semantics.  This module
-- proves that both realizations reconstruct the same initial state and hence
-- the same entire step/run trajectory.
------------------------------------------------------------------------

binaryInitialState : Machine.MachineState
binaryInitialState =
  Machine.machineState
    0
    (Storage.decodeBinaryMemory Storage.helloProgramBinaryStorage)
    (Storage.decodeBinaryMemory Storage.helloDataBinaryStorage)
    Machine.emptyRegisters
    []
    false
    0

ternary27InitialState : Machine.MachineState
ternary27InitialState =
  Machine.machineState
    0
    (Storage.decodeTernary27Memory Storage.helloProgramTernary27Storage)
    (Storage.decodeTernary27Memory Storage.helloDataTernary27Storage)
    Machine.emptyRegisters
    []
    false
    0

binaryInitialStateIsCanonical :
  binaryInitialState ≡ Machine.initialState
binaryInitialStateIsCanonical
  rewrite Storage.helloProgramBinaryDecodesExactly
        | Storage.helloDataBinaryDecodesExactly = refl

ternary27InitialStateIsCanonical :
  ternary27InitialState ≡ Machine.initialState
ternary27InitialStateIsCanonical
  rewrite Storage.helloProgramTernary27DecodesExactly
        | Storage.helloDataTernary27DecodesExactly = refl

binaryAndTernaryInitialStatesSame :
  binaryInitialState ≡ ternary27InitialState
binaryAndTernaryInitialStatesSame
  rewrite binaryInitialStateIsCanonical
        | ternary27InitialStateIsCanonical = refl

------------------------------------------------------------------------
-- Full state path, including the initial state and every subsequent state.
------------------------------------------------------------------------

machineTrajectory : Nat → Machine.MachineState → List Machine.MachineState
machineTrajectory 0 state = state ∷ []
machineTrajectory (suc fuel) state =
  state ∷ machineTrajectory fuel (Machine.step state)

binaryTrajectory : List Machine.MachineState
binaryTrajectory = machineTrajectory 14 binaryInitialState

ternary27Trajectory : List Machine.MachineState
ternary27Trajectory = machineTrajectory 14 ternary27InitialState

canonicalTrajectory : List Machine.MachineState
canonicalTrajectory = machineTrajectory 14 Machine.initialState

binaryTrajectoryIsCanonical :
  binaryTrajectory ≡ canonicalTrajectory
binaryTrajectoryIsCanonical
  rewrite binaryInitialStateIsCanonical = refl

ternary27TrajectoryIsCanonical :
  ternary27Trajectory ≡ canonicalTrajectory
ternary27TrajectoryIsCanonical
  rewrite ternary27InitialStateIsCanonical = refl

binaryAndTernaryTrajectoriesSame :
  binaryTrajectory ≡ ternary27Trajectory
binaryAndTernaryTrajectoriesSame
  rewrite binaryTrajectoryIsCanonical
        | ternary27TrajectoryIsCanonical = refl

------------------------------------------------------------------------
-- Same final machine state, registers, output, PC and halt status.
------------------------------------------------------------------------

binaryFinalState : Machine.MachineState
binaryFinalState = Machine.runFuel 14 binaryInitialState

ternary27FinalState : Machine.MachineState
ternary27FinalState = Machine.runFuel 14 ternary27InitialState

binaryFinalIsCanonical :
  binaryFinalState ≡ Machine.canonicalFinalState
binaryFinalIsCanonical
  rewrite binaryInitialStateIsCanonical = refl

ternary27FinalIsCanonical :
  ternary27FinalState ≡ Machine.canonicalFinalState
ternary27FinalIsCanonical
  rewrite ternary27InitialStateIsCanonical = refl

binaryAndTernaryFinalStatesSame :
  binaryFinalState ≡ ternary27FinalState
binaryAndTernaryFinalStatesSame
  rewrite binaryFinalIsCanonical
        | ternary27FinalIsCanonical = refl

binaryOutputExact :
  Machine.outputTape binaryFinalState ≡ Machine.helloWorldCodes
binaryOutputExact
  rewrite binaryFinalIsCanonical = Machine.canonicalEncodedOutputExact

ternary27OutputExact :
  Machine.outputTape ternary27FinalState ≡ Machine.helloWorldCodes
ternary27OutputExact
  rewrite ternary27FinalIsCanonical = Machine.canonicalEncodedOutputExact

binaryRegistersEqualTernaryRegisters :
  Machine.registers binaryFinalState ≡ Machine.registers ternary27FinalState
binaryRegistersEqualTernaryRegisters
  rewrite binaryAndTernaryFinalStatesSame = refl

binaryPCEqualsTernaryPC :
  Machine.pc binaryFinalState ≡ Machine.pc ternary27FinalState
binaryPCEqualsTernaryPC
  rewrite binaryAndTernaryFinalStatesSame = refl

------------------------------------------------------------------------
-- Same semantic execution path, different representation costs.
------------------------------------------------------------------------

binaryPath : Complexity.ExecutionFibrePath Machine.MachineState
binaryPath = Complexity.executionFibrePath binaryTrajectory

ternary27Path : Complexity.ExecutionFibrePath Machine.MachineState
ternary27Path = Complexity.executionFibrePath ternary27Trajectory

binaryTransitionCost : Nat
binaryTransitionCost =
  Complexity.K Complexity.transitionConsumer binaryPath

ternary27TransitionCost : Nat
ternary27TransitionCost =
  Complexity.K Complexity.transitionConsumer ternary27Path

binaryHeadTravelCost : Nat
binaryHeadTravelCost =
  Complexity.K (Complexity.headTravelConsumer Machine.pc) binaryPath

ternary27HeadTravelCost : Nat
ternary27HeadTravelCost =
  Complexity.K (Complexity.headTravelConsumer Machine.pc) ternary27Path

binaryTransitionCostIsFourteen : binaryTransitionCost ≡ 14
binaryTransitionCostIsFourteen = refl

ternary27TransitionCostIsFourteen : ternary27TransitionCost ≡ 14
ternary27TransitionCostIsFourteen = refl

binaryHeadTravelCostIsThirteen : binaryHeadTravelCost ≡ 13
binaryHeadTravelCostIsThirteen = refl

ternary27HeadTravelCostIsThirteen : ternary27HeadTravelCost ≡ 13
ternary27HeadTravelCostIsThirteen = refl

sameTrajectoryMeansSameTransitionConsumer :
  binaryTransitionCost ≡ ternary27TransitionCost
sameTrajectoryMeansSameTransitionConsumer = refl

sameTrajectoryMeansSameHeadTravelConsumer :
  binaryHeadTravelCost ≡ ternary27HeadTravelCost
sameTrajectoryMeansSameHeadTravelConsumer = refl

------------------------------------------------------------------------
-- Representation/storage consumers can differ while execution consumers agree.
------------------------------------------------------------------------

binaryProgramRepresentationCost : Nat
binaryProgramRepresentationCost = Storage.programBinaryCellCost

ternary27ProgramRepresentationCost : Nat
ternary27ProgramRepresentationCost = Storage.programTernary27CellCost

binaryDataRepresentationCost : Nat
binaryDataRepresentationCost = Storage.dataBinaryCellCost

ternary27DataRepresentationCost : Nat
ternary27DataRepresentationCost = Storage.dataTernary27CellCost

binaryProgramRepresentationCostIs126 :
  binaryProgramRepresentationCost ≡ 126
binaryProgramRepresentationCostIs126 = Storage.programBinaryCellCostIs126

ternaryProgramRepresentationCostIs42 :
  ternary27ProgramRepresentationCost ≡ 42
ternaryProgramRepresentationCostIs42 = Storage.programTernary27CellCostIs42

record HelloWorldBinaryTernaryExecutionBidiBoundary : Set where
  constructor helloWorldBinaryTernaryExecutionBidiBoundary
  field
    decodedInitialStatesSame : Bool
    fullExecutionTrajectoriesSame : Bool
    finalRegistersSame : Bool
    finalOutputSame : Bool
    transitionComplexitySame : Bool
    headTravelComplexitySame : Bool
    representationCellComplexitySame : Bool
    fewerLogicalCellsImpliesLowerPhysicalCost : Bool

canonicalHelloWorldBinaryTernaryExecutionBidiBoundary :
  HelloWorldBinaryTernaryExecutionBidiBoundary
canonicalHelloWorldBinaryTernaryExecutionBidiBoundary =
  helloWorldBinaryTernaryExecutionBidiBoundary
    true true true true true true false false
