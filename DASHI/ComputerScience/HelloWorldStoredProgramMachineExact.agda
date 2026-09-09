module DASHI.ComputerScience.HelloWorldStoredProgramMachineExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.HelloWorldFibreExact as Hello
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.ComputerScience.FibreMachineFoundation369Exact as CS

------------------------------------------------------------------------
-- HELLO WORLD: STORED-PROGRAM MACHINE
--
-- The semantic Hello World owner says only what output is required.  This
-- module supplies the first explicit machine realization below that spec:
--
--   PC -> instruction-memory fetch -> decode -> data-memory/register read
--      -> output-tape write -> PC advance -> halt.
--
-- Program memory and symbol memory are separate fibres.  The machine does not
-- bake the message into the output instruction: each output instruction names
-- a data address whose cell is fetched at execution time.
------------------------------------------------------------------------

data Symbol : Set where
  H e l o comma space W r d bang : Symbol

data DataAddress : Set where
  d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 : DataAddress

data PC : Set where
  pc0 pc1 pc2 pc3 pc4 pc5 pc6 pc7 pc8 pc9 pc10 pc11 pc12 pc13 : PC

data Instruction : Set where
  outputFrom : DataAddress -> Instruction
  halt : Instruction

ProgramMemory : Set
ProgramMemory = PC -> Instruction

DataMemory : Set
DataMemory = DataAddress -> Symbol

canonicalDataMemory : DataMemory
canonicalDataMemory d0 = H
canonicalDataMemory d1 = e
canonicalDataMemory d2 = l
canonicalDataMemory d3 = l
canonicalDataMemory d4 = o
canonicalDataMemory d5 = comma
canonicalDataMemory d6 = space
canonicalDataMemory d7 = W
canonicalDataMemory d8 = o
canonicalDataMemory d9 = r
canonicalDataMemory d10 = l
canonicalDataMemory d11 = d
canonicalDataMemory d12 = bang

canonicalProgramMemory : ProgramMemory
canonicalProgramMemory pc0 = outputFrom d0
canonicalProgramMemory pc1 = outputFrom d1
canonicalProgramMemory pc2 = outputFrom d2
canonicalProgramMemory pc3 = outputFrom d3
canonicalProgramMemory pc4 = outputFrom d4
canonicalProgramMemory pc5 = outputFrom d5
canonicalProgramMemory pc6 = outputFrom d6
canonicalProgramMemory pc7 = outputFrom d7
canonicalProgramMemory pc8 = outputFrom d8
canonicalProgramMemory pc9 = outputFrom d9
canonicalProgramMemory pc10 = outputFrom d10
canonicalProgramMemory pc11 = outputFrom d11
canonicalProgramMemory pc12 = outputFrom d12
canonicalProgramMemory pc13 = halt

nextPC : PC -> PC
nextPC pc0 = pc1
nextPC pc1 = pc2
nextPC pc2 = pc3
nextPC pc3 = pc4
nextPC pc4 = pc5
nextPC pc5 = pc6
nextPC pc6 = pc7
nextPC pc7 = pc8
nextPC pc8 = pc9
nextPC pc9 = pc10
nextPC pc10 = pc11
nextPC pc11 = pc12
nextPC pc12 = pc13
nextPC pc13 = pc13

OutputTape : Set
OutputTape = List Symbol

record MachineState : Set where
  constructor machineState
  field
    pc : PC
    programMemory : ProgramMemory
    dataMemory : DataMemory
    outputTape : OutputTape
    halted : Bool
    cycles : Nat

open MachineState public

initialState : MachineState
initialState =
  machineState pc0 canonicalProgramMemory canonicalDataMemory [] false 0

fetchInstruction : MachineState -> Instruction
fetchInstruction state = programMemory state (pc state)

readData : MachineState -> DataAddress -> Symbol
readData state address = dataMemory state address

appendSymbol : OutputTape -> Symbol -> OutputTape
appendSymbol [] symbol = symbol ∷ []
appendSymbol (x ∷ xs) symbol = x ∷ appendSymbol xs symbol

step : MachineState -> MachineState
step state with halted state
... | true = state
... | false with fetchInstruction state
...   | halt =
      machineState
        (pc state)
        (programMemory state)
        (dataMemory state)
        (outputTape state)
        true
        (suc (cycles state))
...   | outputFrom address =
      machineState
        (nextPC (pc state))
        (programMemory state)
        (dataMemory state)
        (appendSymbol (outputTape state) (readData state address))
        false
        (suc (cycles state))

runFuel : Nat -> MachineState -> MachineState
runFuel 0 state = state
runFuel (suc fuel) state = runFuel fuel (step state)

canonicalFinalState : MachineState
canonicalFinalState = runFuel 14 initialState

helloWorldSymbols : OutputTape
helloWorldSymbols =
  H ∷ e ∷ l ∷ l ∷ o ∷ comma ∷ space ∷ W ∷ o ∷ r ∷ l ∷ d ∷ bang ∷ []

canonicalStoredProgramOutputExact :
  outputTape canonicalFinalState ≡ helloWorldSymbols
canonicalStoredProgramOutputExact = refl

canonicalStoredProgramHalts : halted canonicalFinalState ≡ true
canonicalStoredProgramHalts = refl

canonicalStoredProgramCycleCost : cycles canonicalFinalState ≡ 14
canonicalStoredProgramCycleCost = refl

canonicalStoredProgramStopsAtHaltPC : pc canonicalFinalState ≡ pc13
canonicalStoredProgramStopsAtHaltPC = refl

------------------------------------------------------------------------
-- Fetch/decode receipts: representative and terminal coordinates.
------------------------------------------------------------------------

firstInstructionFetchedFromProgramMemory :
  fetchInstruction initialState ≡ outputFrom d0
firstInstructionFetchedFromProgramMemory = refl

firstSymbolFetchedFromDataMemory :
  readData initialState d0 ≡ H
firstSymbolFetchedFromDataMemory = refl

stateAfterOne : MachineState
stateAfterOne = step initialState

firstStepAdvancesProgramCounter : pc stateAfterOne ≡ pc1
firstStepAdvancesProgramCounter = refl

firstStepWritesFetchedSymbol : outputTape stateAfterOne ≡ H ∷ []
firstStepWritesFetchedSymbol = refl

stateBeforeHalt : MachineState
stateBeforeHalt = runFuel 13 initialState

haltInstructionFetchedAtTerminalPC :
  fetchInstruction stateBeforeHalt ≡ halt
haltInstructionFetchedAtTerminalPC = refl

haltStepDoesNotAppendOutput :
  outputTape (step stateBeforeHalt) ≡ outputTape stateBeforeHalt
haltStepDoesNotAppendOutput = refl

------------------------------------------------------------------------
-- Full execution trace.  The trace records the instruction fetched before
-- each machine transition; it is distinct from output and from cycle count.
------------------------------------------------------------------------

record TraceEntry : Set where
  constructor traceEntry
  field
    atPC : PC
    fetched : Instruction

open TraceEntry public

traceFuel : Nat -> MachineState -> List TraceEntry
traceFuel 0 state = []
traceFuel (suc fuel) state =
  traceEntry (pc state) (fetchInstruction state)
  ∷ traceFuel fuel (step state)

canonicalFetchTrace : List TraceEntry
canonicalFetchTrace = traceFuel 14 initialState

expectedFetchTrace : List TraceEntry
expectedFetchTrace =
  traceEntry pc0 (outputFrom d0)
  ∷ traceEntry pc1 (outputFrom d1)
  ∷ traceEntry pc2 (outputFrom d2)
  ∷ traceEntry pc3 (outputFrom d3)
  ∷ traceEntry pc4 (outputFrom d4)
  ∷ traceEntry pc5 (outputFrom d5)
  ∷ traceEntry pc6 (outputFrom d6)
  ∷ traceEntry pc7 (outputFrom d7)
  ∷ traceEntry pc8 (outputFrom d8)
  ∷ traceEntry pc9 (outputFrom d9)
  ∷ traceEntry pc10 (outputFrom d10)
  ∷ traceEntry pc11 (outputFrom d11)
  ∷ traceEntry pc12 (outputFrom d12)
  ∷ traceEntry pc13 halt
  ∷ []

canonicalFetchTraceExact : canonicalFetchTrace ≡ expectedFetchTrace
canonicalFetchTraceExact = refl

------------------------------------------------------------------------
-- Semantic refinement to the high-level Hello World spec.
--
-- The symbol machine has a richer alphabet than the one-token semantic owner,
-- so the refinement is explicit: the exact symbol tape is recognized as the
-- high-level `helloWorld` message.  No C/Rust/ISA/compiler claim is made here.
------------------------------------------------------------------------

recogniseHelloWorld : OutputTape -> Hello.Output
recogniseHelloWorld
  (H ∷ e ∷ l ∷ l ∷ o ∷ comma ∷ space ∷ W ∷ o ∷ r ∷ l ∷ d ∷ bang ∷ []) =
  Hello.helloWorld ∷ []
recogniseHelloWorld tape = []

storedProgramRefinesHelloWorldSpec :
  recogniseHelloWorld (outputTape canonicalFinalState) ≡ Hello.helloWorldSpec
storedProgramRefinesHelloWorldSpec = refl

------------------------------------------------------------------------
-- Fibre view: complete hidden machine state projects to output.  Runtime cost
-- and trace remain separate consumers and therefore cannot be inferred merely
-- from equality of output without separate sufficiency proofs.
------------------------------------------------------------------------

storedProgramExecutionFibre : CS.ExecutionFibre
storedProgramExecutionFibre =
  CS.executionFibre
    MachineState
    OutputTape
    OutputTape
    Nat
    outputTape
    outputTape
    cycles

storedProgramOutputIsConsumerAdequate :
  CS.ConsumerAdequate storedProgramExecutionFibre
storedProgramOutputIsConsumerAdequate =
  Descent.consumerObserverIsSufficient outputTape

record StoredProgramHelloWorldReceipt : Set where
  constructor storedProgramHelloWorldReceipt
  field
    finalState : MachineState
    outputExact : outputTape finalState ≡ helloWorldSymbols
    haltedExact : halted finalState ≡ true
    terminalPCExact : pc finalState ≡ pc13
    cyclesExact : cycles finalState ≡ 14
    traceExact : canonicalFetchTrace ≡ expectedFetchTrace
    refinesSemanticHelloWorld :
      recogniseHelloWorld (outputTape finalState) ≡ Hello.helloWorldSpec

canonicalStoredProgramHelloWorldReceipt : StoredProgramHelloWorldReceipt
canonicalStoredProgramHelloWorldReceipt =
  storedProgramHelloWorldReceipt
    canonicalFinalState
    canonicalStoredProgramOutputExact
    canonicalStoredProgramHalts
    canonicalStoredProgramStopsAtHaltPC
    canonicalStoredProgramCycleCost
    canonicalFetchTraceExact
    storedProgramRefinesHelloWorldSpec

record StoredProgramBoundary : Set where
  constructor storedProgramBoundary
  field
    programFetchedFromMemory : Bool
    symbolsFetchedFromSeparateDataMemory : Bool
    programCounterExplicit : Bool
    outputTapeExplicit : Bool
    fetchTraceExplicit : Bool
    haltExplicit : Bool
    costSeparateFromOutput : Bool
    physicalRegisterFileClaimed : Bool
    ASICOrFPGARealizationClaimed : Bool

canonicalStoredProgramBoundary : StoredProgramBoundary
canonicalStoredProgramBoundary =
  storedProgramBoundary true true true true true true true false false
