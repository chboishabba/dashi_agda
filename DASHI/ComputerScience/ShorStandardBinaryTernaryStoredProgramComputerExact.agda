module DASHI.ComputerScience.ShorStandardBinaryTernaryStoredProgramComputerExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.ComputerScience.FixedNineBitFramed27WordStorageExact as WordStorage
import DASHI.ComputerScience.EuclidGCDBinaryTernaryRegisterFibreExact as RegisterFibre
import DASHI.ComputerScience.TinyISAClosedProgramCodebookFibreExact as Codebook
import DASHI.ComputerScience.ClassicalOrderFindingRegisterMachineExact as Order
import DASHI.ComputerScience.ModularExponentiationRegisterMachineExact as Pow
import DASHI.ComputerScience.ShorFactoringToClassicalBinaryTernaryMachineExact as Factor

------------------------------------------------------------------------
-- COMPLETE STORED-PROGRAM REALIZATIONS FOR THE CLASSICAL SHOR DESCENT
--
-- A realization consists of:
--   * stored program index words,
--   * a typed decoder/codebook context,
--   * stored register words,
--   * the ordinary radix-neutral machine state reconstructed from both.
--
-- Binary and framed-27 storage therefore realize the same decoded program and
-- same decoded registers, hence the same ordinary execution.  The decoder
-- context remains a provenance/proof coordinate.
------------------------------------------------------------------------

record BinaryStoredComputer : Set where
  constructor binaryStoredComputer
  field
    programWordsB : List WordStorage.BinaryWord9
    registerWordsB : RegisterFibre.BinaryRegisterStorage
    decoderProgramB : Machine.Program

open BinaryStoredComputer public

record TernaryStoredComputer : Set where
  constructor ternaryStoredComputer
  field
    programWordsT : List WordStorage.Ternary27Word3
    registerWordsT : RegisterFibre.Ternary27RegisterStorage
    decoderProgramT : Machine.Program

open TernaryStoredComputer public

rebuildBinaryState : BinaryStoredComputer → Machine.MachineState
rebuildBinaryState C =
  Machine.machineState
    0
    (Codebook.decodeByProgram
      (decoderProgramB C)
      (WordStorage.decodeBinaryMemory (programWordsB C)))
    []
    (RegisterFibre.decodeBinaryRegisters (registerWordsB C))
    [] false 0

rebuildTernaryState : TernaryStoredComputer → Machine.MachineState
rebuildTernaryState C =
  Machine.machineState
    0
    (Codebook.decodeByProgram
      (decoderProgramT C)
      (WordStorage.decodeTernary27Memory (programWordsT C)))
    []
    (RegisterFibre.decodeTernaryRegisters (registerWordsT C))
    [] false 0

------------------------------------------------------------------------
-- Classical order finding for N=15.
------------------------------------------------------------------------

order15BinaryComputer : BinaryStoredComputer
order15BinaryComputer = binaryStoredComputer
  Codebook.orderBinaryProgramStorage
  (RegisterFibre.encodeBinaryRegisters (Machine.registerFile 1 2 0))
  Codebook.order15Program

order15TernaryComputer : TernaryStoredComputer
order15TernaryComputer = ternaryStoredComputer
  Codebook.orderTernaryProgramStorage
  (RegisterFibre.encodeTernaryRegisters (Machine.registerFile 1 2 0))
  Codebook.order15Program

order15BinaryStateIsCanonical :
  rebuildBinaryState order15BinaryComputer
  ≡ Order.orderInitialState 2 15 B369.nonZero
order15BinaryStateIsCanonical = refl

order15TernaryStateIsCanonical :
  rebuildTernaryState order15TernaryComputer
  ≡ Order.orderInitialState 2 15 B369.nonZero
order15TernaryStateIsCanonical = refl

order15BinaryFinal : Machine.MachineState
order15BinaryFinal =
  Machine.runFuel Order.order15Fuel (rebuildBinaryState order15BinaryComputer)

order15TernaryFinal : Machine.MachineState
order15TernaryFinal =
  Machine.runFuel Order.order15Fuel (rebuildTernaryState order15TernaryComputer)

order15BinaryAndTernaryExecutionEqual :
  order15BinaryFinal ≡ order15TernaryFinal
order15BinaryAndTernaryExecutionEqual = refl

order15StoredComputersRecoverFour :
  Machine.output order15BinaryFinal ≡ 4 ∷ []
order15StoredComputersRecoverFour = refl

------------------------------------------------------------------------
-- Classical order finding for N=21.
------------------------------------------------------------------------

order21BinaryComputer : BinaryStoredComputer
order21BinaryComputer = binaryStoredComputer
  Codebook.orderBinaryProgramStorage
  (RegisterFibre.encodeBinaryRegisters (Machine.registerFile 1 2 0))
  Codebook.order21Program

order21TernaryComputer : TernaryStoredComputer
order21TernaryComputer = ternaryStoredComputer
  Codebook.orderTernaryProgramStorage
  (RegisterFibre.encodeTernaryRegisters (Machine.registerFile 1 2 0))
  Codebook.order21Program

order21BinaryStateIsCanonical :
  rebuildBinaryState order21BinaryComputer
  ≡ Order.orderInitialState 2 21 B369.nonZero
order21BinaryStateIsCanonical = refl

order21TernaryStateIsCanonical :
  rebuildTernaryState order21TernaryComputer
  ≡ Order.orderInitialState 2 21 B369.nonZero
order21TernaryStateIsCanonical = refl

order21BinaryFinal : Machine.MachineState
order21BinaryFinal =
  Machine.runFuel Order.order21Fuel (rebuildBinaryState order21BinaryComputer)

order21TernaryFinal : Machine.MachineState
order21TernaryFinal =
  Machine.runFuel Order.order21Fuel (rebuildTernaryState order21TernaryComputer)

order21BinaryAndTernaryExecutionEqual :
  order21BinaryFinal ≡ order21TernaryFinal
order21BinaryAndTernaryExecutionEqual = refl

order21StoredComputersRecoverSix :
  Machine.output order21BinaryFinal ≡ 6 ∷ []
order21StoredComputersRecoverSix = refl

------------------------------------------------------------------------
-- Half-power modular exponentiation: same complete storage architecture.
------------------------------------------------------------------------

pow15BinaryComputer : BinaryStoredComputer
pow15BinaryComputer = binaryStoredComputer
  Codebook.powBinaryProgramStorage
  (RegisterFibre.encodeBinaryRegisters (Machine.registerFile 1 2 2))
  Codebook.pow15Program

pow15TernaryComputer : TernaryStoredComputer
pow15TernaryComputer = ternaryStoredComputer
  Codebook.powTernaryProgramStorage
  (RegisterFibre.encodeTernaryRegisters (Machine.registerFile 1 2 2))
  Codebook.pow15Program

pow15BinaryStateIsCanonical :
  rebuildBinaryState pow15BinaryComputer
  ≡ Pow.powModInitialState 2 2 15 B369.nonZero
pow15BinaryStateIsCanonical = refl

pow15TernaryStateIsCanonical :
  rebuildTernaryState pow15TernaryComputer
  ≡ Pow.powModInitialState 2 2 15 B369.nonZero
pow15TernaryStateIsCanonical = refl

pow15StoredComputersProduceFour :
  Machine.output
    (Machine.runFuel (Pow.powModFuel 2) (rebuildBinaryState pow15BinaryComputer))
  ≡ 4 ∷ []
pow15StoredComputersProduceFour = refl

pow21BinaryComputer : BinaryStoredComputer
pow21BinaryComputer = binaryStoredComputer
  Codebook.powBinaryProgramStorage
  (RegisterFibre.encodeBinaryRegisters (Machine.registerFile 1 2 3))
  Codebook.pow21Program

pow21TernaryComputer : TernaryStoredComputer
pow21TernaryComputer = ternaryStoredComputer
  Codebook.powTernaryProgramStorage
  (RegisterFibre.encodeTernaryRegisters (Machine.registerFile 1 2 3))
  Codebook.pow21Program

pow21StoredComputersProduceEight :
  Machine.output
    (Machine.runFuel (Pow.powModFuel 3) (rebuildTernaryState pow21TernaryComputer))
  ≡ 8 ∷ []
pow21StoredComputersProduceEight = refl

------------------------------------------------------------------------
-- Representation costs for a complete six-instruction/three-register machine
-- snapshot. These remain logical storage-cell counts only.
------------------------------------------------------------------------

binarySixInstructionThreeRegisterCells : Nat
binarySixInstructionThreeRegisterCells =
  Codebook.sixInstructionBinaryProgramCellCost
  + RegisterFibre.binaryRegisterCellCost

ternarySixInstructionThreeRegisterCells : Nat
ternarySixInstructionThreeRegisterCells =
  Codebook.sixInstructionTernaryProgramCellCost
  + RegisterFibre.ternary27RegisterCellCost

binaryCompleteCellsIs81 : binarySixInstructionThreeRegisterCells ≡ 81
binaryCompleteCellsIs81 = refl

ternaryCompleteCellsIs27 : ternarySixInstructionThreeRegisterCells ≡ 27
ternaryCompleteCellsIs27 = refl

record StandardBinaryTernaryStoredProgramBoundary : Set where
  constructor standardBinaryTernaryStoredProgramBoundary
  field
    programMemoryStoredAsWords : Bool
    registerStateStoredAsWords : Bool
    typedDecoderContextExplicit : Bool
    binaryCompleteInitialStateExact : Bool
    ternaryCompleteInitialStateExact : Bool
    sameDecodedExecution : Bool
    orderFindingExecutable : Bool
    modularExponentiationExecutable : Bool
    euclidFactorExtractionExecutable : Bool
    proofContextPretendedToBeRawStorage : Bool
    binaryAndTernaryStorageIdentified : Bool
    logicalCellCountPromotedToPhysicalCost : Bool

canonicalStandardBinaryTernaryStoredProgramBoundary :
  StandardBinaryTernaryStoredProgramBoundary
canonicalStandardBinaryTernaryStoredProgramBoundary =
  standardBinaryTernaryStoredProgramBoundary
    true true true true true true true true true false false false
