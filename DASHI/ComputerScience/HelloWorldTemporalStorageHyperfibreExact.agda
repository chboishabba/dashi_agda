module DASHI.ComputerScience.HelloWorldTemporalStorageHyperfibreExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.TemporalStorageFibreExact as Storage
import DASHI.ComputerScience.HelloWorldEncodedWordMachineExact as Machine
import DASHI.ComputerScience.HelloWorldJacquardExact as Cloth
import DASHI.Algebra.Trit as Trit
import DASHI.Computation.JacquardProofVisibleSurfaceExact as Visible

------------------------------------------------------------------------
-- HELLO WORLD TEMPORAL STORAGE HYPERFIBRE
--
-- The electronic/numeric and textile/Jacquard routes share one structural
-- reading: execution is a time-indexed path through fibres of stored cells.
-- The cell carrier differs by realization (Nat word, trit, visible crossing),
-- but the head/path law is not duplicated.
------------------------------------------------------------------------

machineStateAt : Nat → Machine.MachineState
machineStateAt t = Machine.runFuel t Machine.initialState

------------------------------------------------------------------------
-- Numeric program-memory fibre: the program counter is literally the read head.
------------------------------------------------------------------------

programWordStorage : Storage.TemporalStorageFibre
programWordStorage =
  Storage.temporalStorageFibre
    Nat
    Nat
    Nat
    (λ t address →
      Machine.lookupWord
        (Machine.programMemory (machineStateAt t))
        address)
    (λ t → Machine.pc (machineStateAt t))

programHeadReadsFetchedWord :
  (t : Nat) →
  Storage.readAtHead programWordStorage t
  ≡ Machine.fetchWord (machineStateAt t)
programHeadReadsFetchedWord t = refl

firstProgramHeadAddress : Storage.readHead programWordStorage 0 ≡ 0
firstProgramHeadAddress = refl

firstProgramHeadCell : Storage.readAtHead programWordStorage 0 ≡ 1
firstProgramHeadCell = refl

terminalProgramHeadAddress : Storage.readHead programWordStorage 13 ≡ 13
terminalProgramHeadAddress = refl

terminalProgramHeadCell : Storage.readAtHead programWordStorage 13 ≡ 0
terminalProgramHeadCell = refl

------------------------------------------------------------------------
-- Numeric data-memory fibre.  The active data address is obtained by decoding
-- the current instruction word; HALT has no data operand and is represented by
-- the neutral address 0 only for this total head function.
------------------------------------------------------------------------

activeDataAddress : Machine.MachineState → Nat
activeDataAddress state with Machine.decodeInstruction (Machine.fetchWord state)
... | Machine.haltWord = 0
... | Machine.outputWord address = address

dataWordStorage : Storage.TemporalStorageFibre
dataWordStorage =
  Storage.temporalStorageFibre
    Nat
    Nat
    Nat
    (λ t address →
      Machine.lookupWord
        (Machine.dataMemory (machineStateAt t))
        address)
    (λ t → activeDataAddress (machineStateAt t))

firstDataHeadAddress : Storage.readHead dataWordStorage 0 ≡ 0
firstDataHeadAddress = refl

firstDataHeadCell : Storage.readAtHead dataWordStorage 0 ≡ 72
firstDataHeadCell = refl

------------------------------------------------------------------------
-- Register fibre over time.  Register identity is kept distinct from stored
-- word value and from memory address.
------------------------------------------------------------------------

data RegisterName : Set where
  instructionRegister : RegisterName
  dataRegister : RegisterName

registerValueAt : Nat → RegisterName → Nat
registerValueAt t instructionRegister =
  Machine.instructionRegister (Machine.registers (machineStateAt t))
registerValueAt t dataRegister =
  Machine.dataRegister (Machine.registers (machineStateAt t))

instructionRegisterTimeline : Storage.TemporalRegisterFibre
instructionRegisterTimeline =
  Storage.temporalRegisterFibre
    Nat RegisterName Nat
    registerValueAt
    (λ t → instructionRegister)

dataRegisterTimeline : Storage.TemporalRegisterFibre
dataRegisterTimeline =
  Storage.temporalRegisterFibre
    Nat RegisterName Nat
    registerValueAt
    (λ t → dataRegister)

instructionRegisterAfterFirstCycle :
  Storage.readActiveRegister instructionRegisterTimeline 1 ≡ 1
instructionRegisterAfterFirstCycle = refl

dataRegisterAfterFirstCycle :
  Storage.readActiveRegister dataRegisterTimeline 1 ≡ 72
dataRegisterAfterFirstCycle = refl

------------------------------------------------------------------------
-- Jacquard source-serialization fibre.
--
-- Here time is the read-head index over the three serialized balanced trits.
-- This is not a claim that loom time, CPU cycles, and serialization index are
-- physically identical; they instantiate the same typed temporal-head shape.
------------------------------------------------------------------------

lookupTrit : List Trit.Trit → Nat → Trit.Trit
lookupTrit [] address = Trit.zer
lookupTrit (trit ∷ trits) 0 = trit
lookupTrit (trit ∷ trits) (suc address) = lookupTrit trits address

helloTritStorage : Storage.TemporalStorageFibre
helloTritStorage =
  Storage.temporalStorageFibre
    Nat
    Nat
    Trit.Trit
    (λ t address → lookupTrit Cloth.helloWorldTritStream address)
    (λ t → t)

helloTritRead0 : Storage.readAtHead helloTritStorage 0 ≡ Trit.neg
helloTritRead0 = refl

helloTritRead1 : Storage.readAtHead helloTritStorage 1 ≡ Trit.zer
helloTritRead1 = refl

helloTritRead2 : Storage.readAtHead helloTritStorage 2 ≡ Trit.pos
helloTritRead2 = refl

------------------------------------------------------------------------
-- Visible-cloth storage fibre.  The visible face is another projection of the
-- same Hello World realization, not the source semantics itself.
------------------------------------------------------------------------

lookupVisible : List Visible.VisibleRow2 → Nat → Visible.VisibleRow2
lookupVisible [] address = false , false
lookupVisible (row ∷ rows) 0 = row
lookupVisible (row ∷ rows) (suc address) = lookupVisible rows address

helloVisibleStorage : Storage.TemporalStorageFibre
helloVisibleStorage =
  Storage.temporalStorageFibre
    Nat
    Nat
    Visible.VisibleRow2
    (λ t address → lookupVisible Cloth.helloWorldVisiblePattern address)
    (λ t → t)

record HelloWorldTemporalHyperfibreBoundary : Set where
  constructor helloWorldTemporalHyperfibreBoundary
  field
    programCounterIsProgramReadHead : Bool
    dataOperandSelectsDataFibreHead : Bool
    registersAreTimeIndexedFibres : Bool
    jacquardTritsUseSameHeadShape : Bool
    visibleClothUsesSameHeadShape : Bool
    cpuCycleEqualsLoomTime : Bool
    storageCellEqualsPhysicalMaterial : Bool

canonicalHelloWorldTemporalHyperfibreBoundary :
  HelloWorldTemporalHyperfibreBoundary
canonicalHelloWorldTemporalHyperfibreBoundary =
  helloWorldTemporalHyperfibreBoundary
    true true true true true false false
