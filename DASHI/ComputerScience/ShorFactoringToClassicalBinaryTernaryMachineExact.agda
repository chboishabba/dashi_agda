module DASHI.ComputerScience.ShorFactoringToClassicalBinaryTernaryMachineExact where

open import DASHI.Core.Prelude
open import Data.Nat.GCD using (gcd)

import DASHI.Crypto.FiniteFactorArithmetic as Factor
import DASHI.Crypto.ShorFactoring as Shor
import DASHI.Crypto.ShorConcreteExamples as Examples
import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.ComputerScience.EuclidGCDRegisterMachineExact as Euclid
import DASHI.ComputerScience.EuclidGCDBinaryTernaryRegisterFibreExact as RegisterFibre

------------------------------------------------------------------------
-- FACTORING -> ORDINARY MACHINE DESCENT
--
-- Shor's certified split already supplies the post-processing branch x-1 or
-- x+1.  The standard classical task below is exactly gcd(N, branchValue).
-- We run that task on the existing radix-neutral Euclid machine and then use
-- the existing 9-bit and framed-27 register representations.  No second
-- factoring semantics or codec is introduced.
------------------------------------------------------------------------

shor15BranchValue : Nat
shor15BranchValue = Factor.halfPower Factor.shorSplit15 ∸ 1

shor21BranchValue : Nat
shor21BranchValue = Factor.halfPower Factor.shorSplit21 ∸ 1

shor15BranchValueIsThree : shor15BranchValue ≡ 3
shor15BranchValueIsThree = refl

shor21BranchValueIsSeven : shor21BranchValue ≡ 7
shor21BranchValueIsSeven = refl

------------------------------------------------------------------------
-- 15 = 3 * 5.
------------------------------------------------------------------------

shor15EuclidRegisters : Machine.RegisterFile
shor15EuclidRegisters = Machine.registerFile 15 shor15BranchValue 0

shor15BinaryRegisters : RegisterFibre.BinaryRegisterStorage
shor15BinaryRegisters = RegisterFibre.encodeBinaryRegisters shor15EuclidRegisters

shor15TernaryRegisters : RegisterFibre.Ternary27RegisterStorage
shor15TernaryRegisters = RegisterFibre.encodeTernaryRegisters shor15EuclidRegisters

shor15BinaryRegistersDecodeExactly :
  RegisterFibre.decodeBinaryRegisters shor15BinaryRegisters ≡ shor15EuclidRegisters
shor15BinaryRegistersDecodeExactly = refl

shor15TernaryRegistersDecodeExactly :
  RegisterFibre.decodeTernaryRegisters shor15TernaryRegisters ≡ shor15EuclidRegisters
shor15TernaryRegistersDecodeExactly = refl

shor15BinaryInitial : Machine.MachineState
shor15BinaryInitial =
  Machine.machineState 0 Euclid.euclidProgram []
    (RegisterFibre.decodeBinaryRegisters shor15BinaryRegisters)
    [] false 0

shor15TernaryInitial : Machine.MachineState
shor15TernaryInitial =
  Machine.machineState 0 Euclid.euclidProgram []
    (RegisterFibre.decodeTernaryRegisters shor15TernaryRegisters)
    [] false 0

shor15Fuel : Nat
shor15Fuel = 19

shor15BinaryFinal : Machine.MachineState
shor15BinaryFinal = Machine.runFuel shor15Fuel shor15BinaryInitial

shor15TernaryFinal : Machine.MachineState
shor15TernaryFinal = Machine.runFuel shor15Fuel shor15TernaryInitial

shor15BinaryOutput : Machine.output shor15BinaryFinal ≡ 3 ∷ []
shor15BinaryOutput = refl

shor15TernaryOutput : Machine.output shor15TernaryFinal ≡ 3 ∷ []
shor15TernaryOutput = refl

shor15BinaryAndTernaryFinalEqual : shor15BinaryFinal ≡ shor15TernaryFinal
shor15BinaryAndTernaryFinalEqual = refl

shor15MachineMatchesLibraryGcd :
  Machine.reg0 (Machine.registers shor15BinaryFinal) ≡ gcd 15 shor15BranchValue
shor15MachineMatchesLibraryGcd = refl

shor15MachineMatchesCertifiedShorFactor :
  Machine.reg0 (Machine.registers shor15BinaryFinal)
  ≡ proj₁ (Shor.classicalShorFactor Examples.shor15Problem)
shor15MachineMatchesCertifiedShorFactor = refl

------------------------------------------------------------------------
-- 21 = 7 * 3.
------------------------------------------------------------------------

shor21EuclidRegisters : Machine.RegisterFile
shor21EuclidRegisters = Machine.registerFile 21 shor21BranchValue 0

shor21BinaryRegisters : RegisterFibre.BinaryRegisterStorage
shor21BinaryRegisters = RegisterFibre.encodeBinaryRegisters shor21EuclidRegisters

shor21TernaryRegisters : RegisterFibre.Ternary27RegisterStorage
shor21TernaryRegisters = RegisterFibre.encodeTernaryRegisters shor21EuclidRegisters

shor21BinaryRegistersDecodeExactly :
  RegisterFibre.decodeBinaryRegisters shor21BinaryRegisters ≡ shor21EuclidRegisters
shor21BinaryRegistersDecodeExactly = refl

shor21TernaryRegistersDecodeExactly :
  RegisterFibre.decodeTernaryRegisters shor21TernaryRegisters ≡ shor21EuclidRegisters
shor21TernaryRegistersDecodeExactly = refl

shor21BinaryInitial : Machine.MachineState
shor21BinaryInitial =
  Machine.machineState 0 Euclid.euclidProgram []
    (RegisterFibre.decodeBinaryRegisters shor21BinaryRegisters)
    [] false 0

shor21TernaryInitial : Machine.MachineState
shor21TernaryInitial =
  Machine.machineState 0 Euclid.euclidProgram []
    (RegisterFibre.decodeTernaryRegisters shor21TernaryRegisters)
    [] false 0

shor21Fuel : Nat
shor21Fuel = 11

shor21BinaryFinal : Machine.MachineState
shor21BinaryFinal = Machine.runFuel shor21Fuel shor21BinaryInitial

shor21TernaryFinal : Machine.MachineState
shor21TernaryFinal = Machine.runFuel shor21Fuel shor21TernaryInitial

shor21BinaryOutput : Machine.output shor21BinaryFinal ≡ 7 ∷ []
shor21BinaryOutput = refl

shor21TernaryOutput : Machine.output shor21TernaryFinal ≡ 7 ∷ []
shor21TernaryOutput = refl

shor21BinaryAndTernaryFinalEqual : shor21BinaryFinal ≡ shor21TernaryFinal
shor21BinaryAndTernaryFinalEqual = refl

shor21MachineMatchesLibraryGcd :
  Machine.reg0 (Machine.registers shor21BinaryFinal) ≡ gcd 21 shor21BranchValue
shor21MachineMatchesLibraryGcd = refl

shor21MachineMatchesCertifiedShorFactor :
  Machine.reg0 (Machine.registers shor21BinaryFinal)
  ≡ proj₁ (Shor.classicalShorFactor Examples.shor21Problem)
shor21MachineMatchesCertifiedShorFactor = refl

------------------------------------------------------------------------
-- Same factoring consumer, peer ordinary storage fibres.
------------------------------------------------------------------------

record ShorToClassicalMachineReceipt : Set where
  constructor shorToClassicalMachineReceipt
  field
    shor15SplitDescendsToEuclid : Bool
    shor21SplitDescendsToEuclid : Bool
    binaryAndTernaryRecoverSameInputs : Bool
    binaryAndTernaryRunSameAbstractMachine : Bool
    binaryAndTernaryRecoverSameFactors : Bool
    machineFactorMatchesCertifiedShorFactor : Bool
    quantumExecutionIdentifiedWithClassicalEuclidPath : Bool
    binaryStorageIdentifiedWithTernaryStorage : Bool
    physicalCostComparisonClaimed : Bool

canonicalShorToClassicalMachineReceipt : ShorToClassicalMachineReceipt
canonicalShorToClassicalMachineReceipt =
  shorToClassicalMachineReceipt
    true true true true true true false false false
