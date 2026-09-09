module DASHI.ComputerScience.HelloWorldBinaryTernaryFramedWordStorageExact where

open import DASHI.Core.Prelude
open import DASHI.ComputerScience.FixedNineBitFramed27WordStorageExact public

import DASHI.ComputerScience.HelloWorldEncodedWordMachineExact as Machine

------------------------------------------------------------------------
-- HELLO WORLD FIXTURE OVER THE GENERIC FIXED-NINE-BIT / FRAMED-27 OWNER
--
-- Representation mechanics are owned by
-- FixedNineBitFramed27WordStorageExact.  This module now contains only the
-- bounded Hello World memory receipts and representation-cost observations.
------------------------------------------------------------------------

helloProgramBinaryStorage : List BinaryWord9
helloProgramBinaryStorage = encodeBinaryMemory Machine.canonicalProgramMemory

helloDataBinaryStorage : List BinaryWord9
helloDataBinaryStorage = encodeBinaryMemory Machine.canonicalDataMemory

helloProgramTernary27Storage : List Ternary27Word3
helloProgramTernary27Storage = encodeTernary27Memory Machine.canonicalProgramMemory

helloDataTernary27Storage : List Ternary27Word3
helloDataTernary27Storage = encodeTernary27Memory Machine.canonicalDataMemory

helloProgramBinaryDecodesExactly :
  decodeBinaryMemory helloProgramBinaryStorage ≡ Machine.canonicalProgramMemory
helloProgramBinaryDecodesExactly = refl

helloDataBinaryDecodesExactly :
  decodeBinaryMemory helloDataBinaryStorage ≡ Machine.canonicalDataMemory
helloDataBinaryDecodesExactly = refl

helloProgramTernary27DecodesExactly :
  decodeTernary27Memory helloProgramTernary27Storage ≡ Machine.canonicalProgramMemory
helloProgramTernary27DecodesExactly = refl

helloDataTernary27DecodesExactly :
  decodeTernary27Memory helloDataTernary27Storage ≡ Machine.canonicalDataMemory
helloDataTernary27DecodesExactly = refl

programWordCount : Nat
programWordCount = 14

dataWordCount : Nat
dataWordCount = 13

programBinaryCellCost : Nat
programBinaryCellCost = programWordCount * binaryCellsPerWord

programTernary27CellCost : Nat
programTernary27CellCost = programWordCount * ternary27CellsPerWord

dataBinaryCellCost : Nat
dataBinaryCellCost = dataWordCount * binaryCellsPerWord

dataTernary27CellCost : Nat
dataTernary27CellCost = dataWordCount * ternary27CellsPerWord

programBinaryCellCostIs126 : programBinaryCellCost ≡ 126
programBinaryCellCostIs126 = refl

programTernary27CellCostIs42 : programTernary27CellCost ≡ 42
programTernary27CellCostIs42 = refl

dataBinaryCellCostIs117 : dataBinaryCellCost ≡ 117
dataBinaryCellCostIs117 = refl

dataTernary27CellCostIs39 : dataTernary27CellCost ≡ 39
dataTernary27CellCostIs39 = refl

record HelloWorldBinaryTernaryFramedWordBoundary : Set where
  constructor helloWorldBinaryTernaryFramedWordBoundary
  field
    sameNumericProgramRecovered : Bool
    sameNumericDataRecovered : Bool
    binaryWordWidthExplicit : Bool
    ternaryUsesThreeFramed27CellsPerWord : Bool
    paddingHidden : Bool
    genericAllNatCodecClaimed : Bool
    fewerLogicalCellsImpliesLowerPhysicalCost : Bool
    representationCodecHasGenericOwner : Bool

canonicalHelloWorldBinaryTernaryFramedWordBoundary :
  HelloWorldBinaryTernaryFramedWordBoundary
canonicalHelloWorldBinaryTernaryFramedWordBoundary =
  helloWorldBinaryTernaryFramedWordBoundary
    true true true true false false false true
