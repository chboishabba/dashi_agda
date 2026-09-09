module DASHI.ComputerScience.HelloWorldEncodedWordMachineExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.HelloWorldFibreExact as Hello

------------------------------------------------------------------------
-- HELLO WORLD: ENCODED WORD / REGISTER MACHINE
--
-- This is a refinement below the symbolic stored-program owner.  Program and
-- data memory now contain numeric words rather than Agda instruction/symbol
-- constructors.  The radix/bit-width is intentionally not fixed here: binary
-- and balanced-ternary realizations will later prove encodings of this same
-- numeric-word semantics.
--
-- Instruction-word convention:
--   0       = HALT
--   suc n   = OUTPUT data-memory[n]
--
-- Thus decode, address selection, register loading, data read, tape write,
-- program-counter advance, halt, and exact cycle cost are all explicit.
------------------------------------------------------------------------

Word : Set
Word = Nat

Address : Set
Address = Nat

ProgramCounter : Set
ProgramCounter = Nat

ProgramMemory : Set
ProgramMemory = List Word

DataMemory : Set
DataMemory = List Word

OutputTape : Set
OutputTape = List Word

canonicalDataMemory : DataMemory
canonicalDataMemory =
  72 ∷ 101 ∷ 108 ∷ 108 ∷ 111 ∷ 44 ∷ 32 ∷
  87 ∷ 111 ∷ 114 ∷ 108 ∷ 100 ∷ 33 ∷ []

-- Words 1..13 output data addresses 0..12.  Final word 0 halts.
canonicalProgramMemory : ProgramMemory
canonicalProgramMemory =
  1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷
  8 ∷ 9 ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ 0 ∷ []

lookupWord : List Word → Address → Word
lookupWord [] address = 0
lookupWord (word ∷ words) 0 = word
lookupWord (word ∷ words) (suc address) = lookupWord words address

data DecodedInstruction : Set where
  haltWord : DecodedInstruction
  outputWord : Address → DecodedInstruction

decodeInstruction : Word → DecodedInstruction
decodeInstruction 0 = haltWord
decodeInstruction (suc address) = outputWord address

record RegisterFile : Set where
  constructor registerFile
  field
    instructionRegister : Word
    dataRegister : Word

open RegisterFile public

emptyRegisters : RegisterFile
emptyRegisters = registerFile 0 0

record MachineState : Set where
  constructor machineState
  field
    pc : ProgramCounter
    programMemory : ProgramMemory
    dataMemory : DataMemory
    registers : RegisterFile
    outputTape : OutputTape
    halted : Bool
    cycles : Nat

open MachineState public

initialState : MachineState
initialState =
  machineState
    0
    canonicalProgramMemory
    canonicalDataMemory
    emptyRegisters
    []
    false
    0

fetchWord : MachineState → Word
fetchWord state = lookupWord (programMemory state) (pc state)

readDataWord : MachineState → Address → Word
readDataWord state address = lookupWord (dataMemory state) address

appendWord : OutputTape → Word → OutputTape
appendWord [] word = word ∷ []
appendWord (x ∷ xs) word = x ∷ appendWord xs word

step : MachineState → MachineState
step state with halted state
... | true = state
... | false with fetchWord state
...   | fetched with decodeInstruction fetched
...     | haltWord =
        machineState
          (pc state)
          (programMemory state)
          (dataMemory state)
          (registerFile fetched (dataRegister (registers state)))
          (outputTape state)
          true
          (suc (cycles state))
...     | outputWord address =
        machineState
          (suc (pc state))
          (programMemory state)
          (dataMemory state)
          (registerFile fetched (readDataWord state address))
          (appendWord (outputTape state) (readDataWord state address))
          false
          (suc (cycles state))

runFuel : Nat → MachineState → MachineState
runFuel 0 state = state
runFuel (suc fuel) state = runFuel fuel (step state)

canonicalFinalState : MachineState
canonicalFinalState = runFuel 14 initialState

helloWorldCodes : OutputTape
helloWorldCodes = canonicalDataMemory

canonicalEncodedOutputExact :
  outputTape canonicalFinalState ≡ helloWorldCodes
canonicalEncodedOutputExact = refl

canonicalEncodedMachineHalts : halted canonicalFinalState ≡ true
canonicalEncodedMachineHalts = refl

canonicalEncodedMachineCycles : cycles canonicalFinalState ≡ 14
canonicalEncodedMachineCycles = refl

canonicalEncodedMachineTerminalPC : pc canonicalFinalState ≡ 13
canonicalEncodedMachineTerminalPC = refl

canonicalTerminalInstructionRegisterIsHalt :
  instructionRegister (registers canonicalFinalState) ≡ 0
canonicalTerminalInstructionRegisterIsHalt = refl

canonicalTerminalDataRegisterRetainsBang :
  dataRegister (registers canonicalFinalState) ≡ 33
canonicalTerminalDataRegisterRetainsBang = refl

------------------------------------------------------------------------
-- Fetch/decode/data-register receipts for the first machine transition.
------------------------------------------------------------------------

firstFetchedWordIsOutputZero : fetchWord initialState ≡ 1
firstFetchedWordIsOutputZero = refl

firstFetchedWordDecodesToAddressZero :
  decodeInstruction (fetchWord initialState) ≡ outputWord 0
firstFetchedWordDecodesToAddressZero = refl

firstDataReadIsHCode : readDataWord initialState 0 ≡ 72
firstDataReadIsHCode = refl

stateAfterOne : MachineState
stateAfterOne = step initialState

firstStepLoadsInstructionRegister :
  instructionRegister (registers stateAfterOne) ≡ 1
firstStepLoadsInstructionRegister = refl

firstStepLoadsDataRegister :
  dataRegister (registers stateAfterOne) ≡ 72
firstStepLoadsDataRegister = refl

firstStepWritesOutputTape : outputTape stateAfterOne ≡ 72 ∷ []
firstStepWritesOutputTape = refl

firstStepAdvancesPC : pc stateAfterOne ≡ 1
firstStepAdvancesPC = refl

stateBeforeHalt : MachineState
stateBeforeHalt = runFuel 13 initialState

terminalFetchIsHaltWord : fetchWord stateBeforeHalt ≡ 0
terminalFetchIsHaltWord = refl

terminalDecodeIsHalt :
  decodeInstruction (fetchWord stateBeforeHalt) ≡ haltWord
terminalDecodeIsHalt = refl

------------------------------------------------------------------------
-- Word-level trace is separate from extensional output.
------------------------------------------------------------------------

record FetchTraceEntry : Set where
  constructor fetchTraceEntry
  field
    tracePC : ProgramCounter
    fetchedWord : Word

open FetchTraceEntry public

traceFuel : Nat → MachineState → List FetchTraceEntry
traceFuel 0 state = []
traceFuel (suc fuel) state =
  fetchTraceEntry (pc state) (fetchWord state)
  ∷ traceFuel fuel (step state)

canonicalFetchTrace : List FetchTraceEntry
canonicalFetchTrace = traceFuel 14 initialState

expectedFetchTrace : List FetchTraceEntry
expectedFetchTrace =
  fetchTraceEntry 0 1
  ∷ fetchTraceEntry 1 2
  ∷ fetchTraceEntry 2 3
  ∷ fetchTraceEntry 3 4
  ∷ fetchTraceEntry 4 5
  ∷ fetchTraceEntry 5 6
  ∷ fetchTraceEntry 6 7
  ∷ fetchTraceEntry 7 8
  ∷ fetchTraceEntry 8 9
  ∷ fetchTraceEntry 9 10
  ∷ fetchTraceEntry 10 11
  ∷ fetchTraceEntry 11 12
  ∷ fetchTraceEntry 12 13
  ∷ fetchTraceEntry 13 0
  ∷ []

canonicalFetchTraceExact : canonicalFetchTrace ≡ expectedFetchTrace
canonicalFetchTraceExact = refl

------------------------------------------------------------------------
-- Explicit refinement back to semantic Hello World.
------------------------------------------------------------------------

recogniseHelloWorldCodes : OutputTape → Hello.Output
recogniseHelloWorldCodes
  (72 ∷ 101 ∷ 108 ∷ 108 ∷ 111 ∷ 44 ∷ 32 ∷
   87 ∷ 111 ∷ 114 ∷ 108 ∷ 100 ∷ 33 ∷ []) =
  Hello.helloWorld ∷ []
recogniseHelloWorldCodes codes = []

encodedWordMachineRefinesSemanticHelloWorld :
  recogniseHelloWorldCodes (outputTape canonicalFinalState)
  ≡ Hello.helloWorldSpec
encodedWordMachineRefinesSemanticHelloWorld = refl

record EncodedWordHelloWorldReceipt : Set where
  constructor encodedWordHelloWorldReceipt
  field
    finalState : MachineState
    outputExact : outputTape finalState ≡ helloWorldCodes
    haltedExact : halted finalState ≡ true
    pcExact : pc finalState ≡ 13
    cyclesExact : cycles finalState ≡ 14
    instructionRegisterExact :
      instructionRegister (registers finalState) ≡ 0
    dataRegisterExact : dataRegister (registers finalState) ≡ 33
    fetchTraceExact : canonicalFetchTrace ≡ expectedFetchTrace
    semanticRefinement :
      recogniseHelloWorldCodes (outputTape finalState) ≡ Hello.helloWorldSpec

canonicalEncodedWordHelloWorldReceipt : EncodedWordHelloWorldReceipt
canonicalEncodedWordHelloWorldReceipt =
  encodedWordHelloWorldReceipt
    canonicalFinalState
    canonicalEncodedOutputExact
    canonicalEncodedMachineHalts
    canonicalEncodedMachineTerminalPC
    canonicalEncodedMachineCycles
    canonicalTerminalInstructionRegisterIsHalt
    canonicalTerminalDataRegisterRetainsBang
    canonicalFetchTraceExact
    encodedWordMachineRefinesSemanticHelloWorld

record EncodedWordMachineBoundary : Set where
  constructor encodedWordMachineBoundary
  field
    programMemoryContainsWords : Bool
    dataMemoryContainsWords : Bool
    fetchDecodeExplicit : Bool
    registerLoadsExplicit : Bool
    outputPortTapeExplicit : Bool
    radixFixedAtThisLayer : Bool
    bitWidthFixedAtThisLayer : Bool
    binaryRealizationClaimed : Bool
    balancedTernaryRealizationClaimed : Bool

canonicalEncodedWordMachineBoundary : EncodedWordMachineBoundary
canonicalEncodedWordMachineBoundary =
  encodedWordMachineBoundary
    true true true true true false false false false
