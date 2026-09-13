module DASHI.ComputerScience.ModularExponentiationRegisterMachineExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.Crypto.RSAArithmeticCore as RSA
import DASHI.Crypto.FiniteFactorArithmetic as Factor
import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.ComputerScience.FibreProgramComplexityExact as Complexity
import DASHI.ComputerScience.EuclidGCDBinaryTernaryRegisterFibreExact as RegisterFibre

------------------------------------------------------------------------
-- ORDINARY-MACHINE MODULAR EXPONENTIATION
--
-- r0 = accumulator, initialized to 1
-- r1 = base
-- r2 = remaining exponent
--
-- 0: JZ      r2 4
-- 1: MULMOD  r0 r1 modulus
-- 2: SUBI    r2 1
-- 3: JMP     0
-- 4: OUT     r0
-- 5: HALT
--
-- The modulus nonzero witness is carried by MULMOD itself.  This machine is a
-- concrete producer for the existing RSAArithmeticCore.powMod observable; it
-- does not redefine the mathematical arithmetic surface.
------------------------------------------------------------------------

powModProgram :
  (modulus : Nat) →
  B369.NonZero modulus →
  Machine.Program
powModProgram modulus modulusNonZero =
  Machine.jumpIfZero Machine.r2 4
  ∷ Machine.multiplyModulo Machine.r0 Machine.r1 modulus modulusNonZero
  ∷ Machine.subImmediate Machine.r2 1
  ∷ Machine.jump 0
  ∷ Machine.outputRegister Machine.r0
  ∷ Machine.halt
  ∷ []

powModInitialState :
  (base exponent modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Machine.MachineState
powModInitialState base exponent modulus modulusNonZero =
  Machine.machineState
    0
    (powModProgram modulus modulusNonZero)
    []
    (Machine.registerFile 1 base exponent)
    []
    false
    0

powModFuel : Nat → Nat
powModFuel exponent = 4 * exponent + 3

powModMachine :
  (base exponent modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Machine.MachineState
powModMachine base exponent modulus modulusNonZero =
  Machine.runFuel
    (powModFuel exponent)
    (powModInitialState base exponent modulus modulusNonZero)

traceFuel : Nat → Machine.MachineState → List Machine.MachineState
traceFuel zero state = state ∷ []
traceFuel (suc fuel) state = state ∷ traceFuel fuel (Machine.step state)

powModPath :
  (base exponent modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Complexity.ExecutionFibrePath Machine.MachineState
powModPath base exponent modulus modulusNonZero =
  Complexity.executionFibrePath
    (traceFuel
      (powModFuel exponent)
      (powModInitialState base exponent modulus modulusNonZero))

------------------------------------------------------------------------
-- Shor N=15, a=2: half order e=2 gives x=4; full order e=4 gives 1.
------------------------------------------------------------------------

pow2Half15 : Machine.MachineState
pow2Half15 = powModMachine 2 2 15 B369.nonZero

pow2Half15Output : Machine.output pow2Half15 ≡ 4 ∷ []
pow2Half15Output = refl

pow2Half15Accumulator :
  Machine.reg0 (Machine.registers pow2Half15) ≡ 4
pow2Half15Accumulator = refl

pow2Half15MatchesRSA :
  Machine.reg0 (Machine.registers pow2Half15)
  ≡ RSA.powMod 2 2 15 {{B369.nonZero}}
pow2Half15MatchesRSA = refl

pow2Half15MatchesCertifiedHalfPower :
  Machine.reg0 (Machine.registers pow2Half15)
  ≡ Factor.halfPower Factor.shorSplit15
pow2Half15MatchesCertifiedHalfPower = refl

pow2Order15 : Machine.MachineState
pow2Order15 = powModMachine 2 4 15 B369.nonZero

pow2Order15IsOne : Machine.reg0 (Machine.registers pow2Order15) ≡ 1
pow2Order15IsOne = refl

pow2Order15MatchesPeriodLaw :
  Machine.reg0 (Machine.registers pow2Order15)
  ≡ RSA.powMod 2 4 15 {{B369.nonZero}}
pow2Order15MatchesPeriodLaw = refl

pow2Half15Transitions :
  Complexity.K Complexity.transitionConsumer
    (powModPath 2 2 15 B369.nonZero)
  ≡ 11
pow2Half15Transitions = refl

pow2Half15StateVisits :
  Complexity.K Complexity.stateVisitConsumer
    (powModPath 2 2 15 B369.nonZero)
  ≡ 12
pow2Half15StateVisits = refl

------------------------------------------------------------------------
-- Shor N=21, a=2: half order e=3 gives x=8; full order e=6 gives 1.
------------------------------------------------------------------------

pow2Half21 : Machine.MachineState
pow2Half21 = powModMachine 2 3 21 B369.nonZero

pow2Half21Output : Machine.output pow2Half21 ≡ 8 ∷ []
pow2Half21Output = refl

pow2Half21Accumulator :
  Machine.reg0 (Machine.registers pow2Half21) ≡ 8
pow2Half21Accumulator = refl

pow2Half21MatchesRSA :
  Machine.reg0 (Machine.registers pow2Half21)
  ≡ RSA.powMod 2 3 21 {{B369.nonZero}}
pow2Half21MatchesRSA = refl

pow2Half21MatchesCertifiedHalfPower :
  Machine.reg0 (Machine.registers pow2Half21)
  ≡ Factor.halfPower Factor.shorSplit21
pow2Half21MatchesCertifiedHalfPower = refl

pow2Order21 : Machine.MachineState
pow2Order21 = powModMachine 2 6 21 B369.nonZero

pow2Order21IsOne : Machine.reg0 (Machine.registers pow2Order21) ≡ 1
pow2Order21IsOne = refl

pow2Order21MatchesPeriodLaw :
  Machine.reg0 (Machine.registers pow2Order21)
  ≡ RSA.powMod 2 6 21 {{B369.nonZero}}
pow2Order21MatchesPeriodLaw = refl

pow2Half21Transitions :
  Complexity.K Complexity.transitionConsumer
    (powModPath 2 3 21 B369.nonZero)
  ≡ 15
pow2Half21Transitions = refl

pow2Half21StateVisits :
  Complexity.K Complexity.stateVisitConsumer
    (powModPath 2 3 21 B369.nonZero)
  ≡ 16
pow2Half21StateVisits = refl

------------------------------------------------------------------------
-- Binary / framed-27 register realization of the same powMod starts.
------------------------------------------------------------------------

pow15InitialRegisters : Machine.RegisterFile
pow15InitialRegisters = Machine.registerFile 1 2 2

pow15BinaryRegisters : RegisterFibre.BinaryRegisterStorage
pow15BinaryRegisters = RegisterFibre.encodeBinaryRegisters pow15InitialRegisters

pow15TernaryRegisters : RegisterFibre.Ternary27RegisterStorage
pow15TernaryRegisters = RegisterFibre.encodeTernaryRegisters pow15InitialRegisters

pow15BinaryDecode :
  RegisterFibre.decodeBinaryRegisters pow15BinaryRegisters ≡ pow15InitialRegisters
pow15BinaryDecode = refl

pow15TernaryDecode :
  RegisterFibre.decodeTernaryRegisters pow15TernaryRegisters ≡ pow15InitialRegisters
pow15TernaryDecode = refl

pow21InitialRegisters : Machine.RegisterFile
pow21InitialRegisters = Machine.registerFile 1 2 3

pow21BinaryRegisters : RegisterFibre.BinaryRegisterStorage
pow21BinaryRegisters = RegisterFibre.encodeBinaryRegisters pow21InitialRegisters

pow21TernaryRegisters : RegisterFibre.Ternary27RegisterStorage
pow21TernaryRegisters = RegisterFibre.encodeTernaryRegisters pow21InitialRegisters

pow21BinaryDecode :
  RegisterFibre.decodeBinaryRegisters pow21BinaryRegisters ≡ pow21InitialRegisters
pow21BinaryDecode = refl

pow21TernaryDecode :
  RegisterFibre.decodeTernaryRegisters pow21TernaryRegisters ≡ pow21InitialRegisters
pow21TernaryDecode = refl

record ModularExponentiationMachineBoundary : Set where
  constructor modularExponentiationMachineBoundary
  field
    existingPowModRedefined : Bool
    canonicalTinyMachineReused : Bool
    modulusWitnessPreservedInInstruction : Bool
    shor15HalfPowerRealized : Bool
    shor15PeriodValueRealized : Bool
    shor21HalfPowerRealized : Bool
    shor21PeriodValueRealized : Bool
    binaryAndTernaryRegisterStartsExact : Bool
    genericPowModCorrectnessClosed : Bool
    physicalCostClaimed : Bool

canonicalModularExponentiationMachineBoundary :
  ModularExponentiationMachineBoundary
canonicalModularExponentiationMachineBoundary =
  modularExponentiationMachineBoundary
    false true true true true true true true false false
