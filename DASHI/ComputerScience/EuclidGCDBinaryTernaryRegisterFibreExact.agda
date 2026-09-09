module DASHI.ComputerScience.EuclidGCDBinaryTernaryRegisterFibreExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.ComputerScience.EuclidGCDRegisterMachineExact as Euclid
import DASHI.ComputerScience.HelloWorldBinaryTernaryFramedWordStorageExact as WordStorage

------------------------------------------------------------------------
-- BINARY / FRAMED-27 REGISTER REALIZATIONS OF THE SAME EUCLID MACHINE
--
-- The fixed nine-bit word codec was introduced by the Hello World fixture, but
-- its encode/decode functions are generic over Nat.  Here we reuse that exact
-- representation owner for the first nontrivial algorithm rather than create a
-- second word codec.  All values in this fixture are < 512.
------------------------------------------------------------------------

record BinaryRegisterStorage : Set where
  constructor binaryRegisterStorage
  field
    binaryR0 binaryR1 binaryR2 : WordStorage.BinaryWord9

open BinaryRegisterStorage public

record Ternary27RegisterStorage : Set where
  constructor ternary27RegisterStorage
  field
    ternaryR0 ternaryR1 ternaryR2 : WordStorage.Ternary27Word3

open Ternary27RegisterStorage public

encodeBinaryRegisters : Machine.RegisterFile → BinaryRegisterStorage
encodeBinaryRegisters regs =
  binaryRegisterStorage
    (WordStorage.encodeWord9 (Machine.reg0 regs))
    (WordStorage.encodeWord9 (Machine.reg1 regs))
    (WordStorage.encodeWord9 (Machine.reg2 regs))

decodeBinaryRegisters : BinaryRegisterStorage → Machine.RegisterFile
decodeBinaryRegisters storage =
  Machine.registerFile
    (WordStorage.decodeWord9 (binaryR0 storage))
    (WordStorage.decodeWord9 (binaryR1 storage))
    (WordStorage.decodeWord9 (binaryR2 storage))

encodeTernaryRegisters : Machine.RegisterFile → Ternary27RegisterStorage
encodeTernaryRegisters regs =
  ternary27RegisterStorage
    (WordStorage.binaryWord9ToTernary27 (WordStorage.encodeWord9 (Machine.reg0 regs)))
    (WordStorage.binaryWord9ToTernary27 (WordStorage.encodeWord9 (Machine.reg1 regs)))
    (WordStorage.binaryWord9ToTernary27 (WordStorage.encodeWord9 (Machine.reg2 regs)))

decodeTernaryRegisters : Ternary27RegisterStorage → Machine.RegisterFile
decodeTernaryRegisters storage =
  Machine.registerFile
    (WordStorage.decodeWord9
      (WordStorage.ternary27ToBinaryWord9 (ternaryR0 storage)))
    (WordStorage.decodeWord9
      (WordStorage.ternary27ToBinaryWord9 (ternaryR1 storage)))
    (WordStorage.decodeWord9
      (WordStorage.ternary27ToBinaryWord9 (ternaryR2 storage)))

------------------------------------------------------------------------
-- Exact canonical input fixture.
------------------------------------------------------------------------

euclid4818InitialRegisters : Machine.RegisterFile
euclid4818InitialRegisters = Machine.registerFile 48 18 0

euclid4818BinaryRegisters : BinaryRegisterStorage
euclid4818BinaryRegisters = encodeBinaryRegisters euclid4818InitialRegisters

euclid4818TernaryRegisters : Ternary27RegisterStorage
euclid4818TernaryRegisters = encodeTernaryRegisters euclid4818InitialRegisters

euclid4818BinaryRegistersDecodeExactly :
  decodeBinaryRegisters euclid4818BinaryRegisters ≡ euclid4818InitialRegisters
euclid4818BinaryRegistersDecodeExactly = refl

euclid4818TernaryRegistersDecodeExactly :
  decodeTernaryRegisters euclid4818TernaryRegisters ≡ euclid4818InitialRegisters
euclid4818TernaryRegistersDecodeExactly = refl

binaryDecodedInitialState : Machine.MachineState
binaryDecodedInitialState =
  Machine.machineState
    0 Euclid.euclidProgram []
    (decodeBinaryRegisters euclid4818BinaryRegisters)
    [] false 0

ternaryDecodedInitialState : Machine.MachineState
ternaryDecodedInitialState =
  Machine.machineState
    0 Euclid.euclidProgram []
    (decodeTernaryRegisters euclid4818TernaryRegisters)
    [] false 0

binaryInitialStateIsCanonical :
  binaryDecodedInitialState ≡ Euclid.euclidInitialState 48 18
binaryInitialStateIsCanonical = refl

ternaryInitialStateIsCanonical :
  ternaryDecodedInitialState ≡ Euclid.euclidInitialState 48 18
ternaryInitialStateIsCanonical = refl

binaryRealizedFinal : Machine.MachineState
binaryRealizedFinal = Machine.runFuel Euclid.euclid4818Fuel binaryDecodedInitialState

ternaryRealizedFinal : Machine.MachineState
ternaryRealizedFinal = Machine.runFuel Euclid.euclid4818Fuel ternaryDecodedInitialState

binaryFinalIsCanonical : binaryRealizedFinal ≡ Euclid.euclid4818Final
binaryFinalIsCanonical = refl

ternaryFinalIsCanonical : ternaryRealizedFinal ≡ Euclid.euclid4818Final
ternaryFinalIsCanonical = refl

binaryAndTernaryFinalStatesEqual :
  binaryRealizedFinal ≡ ternaryRealizedFinal
binaryAndTernaryFinalStatesEqual = refl

binaryGcdOutputExact : Machine.output binaryRealizedFinal ≡ 6 ∷ []
binaryGcdOutputExact = refl

ternaryGcdOutputExact : Machine.output ternaryRealizedFinal ≡ 6 ∷ []
ternaryGcdOutputExact = refl

------------------------------------------------------------------------
-- Logical register representation costs.
------------------------------------------------------------------------

binaryRegisterCellCost : Nat
binaryRegisterCellCost = 3 * 9

ternary27RegisterCellCost : Nat
ternary27RegisterCellCost = 3 * 3

binaryRegisterCellCostIs27 : binaryRegisterCellCost ≡ 27
binaryRegisterCellCostIs27 = refl

ternary27RegisterCellCostIs9 : ternary27RegisterCellCost ≡ 9
ternary27RegisterCellCostIs9 = refl

record EuclidBinaryTernaryRegisterReceipt : Set where
  constructor euclidBinaryTernaryRegisterReceipt
  field
    binaryInitialDecodesExactly : Bool
    ternaryInitialDecodesExactly : Bool
    sameAbstractFinalState : Bool
    sameGcdOutput : Bool
    binaryLogicalRegisterCells : Nat
    ternaryLogicalRegisterCells : Nat
    binaryCellCountExact : binaryLogicalRegisterCells ≡ 27
    ternaryCellCountExact : ternaryLogicalRegisterCells ≡ 9
    fewerTernaryLogicalCellsProvesLowerPhysicalCost : Bool

canonicalEuclidBinaryTernaryRegisterReceipt :
  EuclidBinaryTernaryRegisterReceipt
canonicalEuclidBinaryTernaryRegisterReceipt =
  euclidBinaryTernaryRegisterReceipt
    true true true true
    binaryRegisterCellCost
    ternary27RegisterCellCost
    refl refl false
