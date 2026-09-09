module DASHI.ComputerScience.ClassicalOrderFindingRegisterMachineExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.Crypto.ShorFactoring as Shor
import DASHI.Crypto.ShorConcreteExamples as Examples
import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.ComputerScience.FibreProgramComplexityExact as Complexity
import DASHI.ComputerScience.EuclidGCDBinaryTernaryRegisterFibreExact as RegisterFibre

------------------------------------------------------------------------
-- CLASSICAL ORDER FINDING ON THE SAME RADIX-NEUTRAL MACHINE
--
-- r0 = current power residue, initialized to 1
-- r1 = base
-- r2 = positive exponent/order counter, initialized to 0
--
-- 0: MULMOD r0 r1 N
-- 1: ADDI   r2 1
-- 2: JEQI   r0 1 4
-- 3: JMP    0
-- 4: OUT    r2
-- 5: HALT
--
-- This is intentionally the simple linear scan.  It is not presented as a
-- competitive replacement for Shor; it gives the ordinary-machine execution
-- fibre for the same recovered-order consumer.
------------------------------------------------------------------------

orderProgram :
  (modulus : Nat) →
  B369.NonZero modulus →
  Machine.Program
orderProgram modulus modulusNonZero =
  Machine.multiplyModulo Machine.r0 Machine.r1 modulus modulusNonZero
  ∷ Machine.addImmediate Machine.r2 1
  ∷ Machine.jumpIfEqualImmediate Machine.r0 1 4
  ∷ Machine.jump 0
  ∷ Machine.outputRegister Machine.r2
  ∷ Machine.halt
  ∷ []

orderInitialState :
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Machine.MachineState
orderInitialState base modulus modulusNonZero =
  Machine.machineState
    0
    (orderProgram modulus modulusNonZero)
    []
    (Machine.registerFile 1 base 0)
    []
    false
    0

orderFuelFromKnownOrder : Nat → Nat
orderFuelFromKnownOrder r = 4 * r + 1

traceFuel : Nat → Machine.MachineState → List Machine.MachineState
traceFuel zero state = state ∷ []
traceFuel (suc fuel) state = state ∷ traceFuel fuel (Machine.step state)

------------------------------------------------------------------------
-- N=15, a=2: exact order 4.
------------------------------------------------------------------------

order15Fuel : Nat
order15Fuel = orderFuelFromKnownOrder 4

order15Final : Machine.MachineState
order15Final =
  Machine.runFuel order15Fuel (orderInitialState 2 15 B369.nonZero)

order15Output : Machine.output order15Final ≡ 4 ∷ []
order15Output = refl

order15Register : Machine.reg2 (Machine.registers order15Final) ≡ 4
order15Register = refl

order15MatchesShorProblem :
  Machine.reg2 (Machine.registers order15Final)
  ≡ Shor.order Examples.shor15Problem
order15MatchesShorProblem = refl

order15Halts : Machine.halted order15Final ≡ true
order15Halts = refl

order15Cycles : Machine.cycles order15Final ≡ 17
order15Cycles = refl

order15Path : Complexity.ExecutionFibrePath Machine.MachineState
order15Path =
  Complexity.executionFibrePath
    (traceFuel order15Fuel (orderInitialState 2 15 B369.nonZero))

order15Transitions :
  Complexity.K Complexity.transitionConsumer order15Path ≡ 17
order15Transitions = refl

order15StateVisits :
  Complexity.K Complexity.stateVisitConsumer order15Path ≡ 18
order15StateVisits = refl

------------------------------------------------------------------------
-- N=21, a=2: exact order 6.
------------------------------------------------------------------------

order21Fuel : Nat
order21Fuel = orderFuelFromKnownOrder 6

order21Final : Machine.MachineState
order21Final =
  Machine.runFuel order21Fuel (orderInitialState 2 21 B369.nonZero)

order21Output : Machine.output order21Final ≡ 6 ∷ []
order21Output = refl

order21Register : Machine.reg2 (Machine.registers order21Final) ≡ 6
order21Register = refl

order21MatchesShorProblem :
  Machine.reg2 (Machine.registers order21Final)
  ≡ Shor.order Examples.shor21Problem
order21MatchesShorProblem = refl

order21Halts : Machine.halted order21Final ≡ true
order21Halts = refl

order21Cycles : Machine.cycles order21Final ≡ 25
order21Cycles = refl

order21Path : Complexity.ExecutionFibrePath Machine.MachineState
order21Path =
  Complexity.executionFibrePath
    (traceFuel order21Fuel (orderInitialState 2 21 B369.nonZero))

order21Transitions :
  Complexity.K Complexity.transitionConsumer order21Path ≡ 25
order21Transitions = refl

order21StateVisits :
  Complexity.K Complexity.stateVisitConsumer order21Path ≡ 26
order21StateVisits = refl

------------------------------------------------------------------------
-- The same initial register values admit the already-owned binary and ternary
-- representations. The modulus remains a proof-carrying program coordinate.
------------------------------------------------------------------------

orderInitialRegisters : Machine.RegisterFile
orderInitialRegisters = Machine.registerFile 1 2 0

orderBinaryRegisters : RegisterFibre.BinaryRegisterStorage
orderBinaryRegisters = RegisterFibre.encodeBinaryRegisters orderInitialRegisters

orderTernaryRegisters : RegisterFibre.Ternary27RegisterStorage
orderTernaryRegisters = RegisterFibre.encodeTernaryRegisters orderInitialRegisters

orderBinaryRegistersDecodeExactly :
  RegisterFibre.decodeBinaryRegisters orderBinaryRegisters ≡ orderInitialRegisters
orderBinaryRegistersDecodeExactly = refl

orderTernaryRegistersDecodeExactly :
  RegisterFibre.decodeTernaryRegisters orderTernaryRegisters ≡ orderInitialRegisters
orderTernaryRegistersDecodeExactly = refl

record ClassicalOrderFindingBoundary : Set where
  constructor classicalOrderFindingBoundary
  field
    canonicalTinyMachineReused : Bool
    linearOrderScanExecutable : Bool
    order15RecoveredExactly : Bool
    order21RecoveredExactly : Bool
    recoveredOrdersMatchShorProblems : Bool
    binaryRegisterRealizationExact : Bool
    ternary27RegisterRealizationExact : Bool
    classicalScanIdentifiedWithQuantumOrderFindingPath : Bool
    genericOrderCorrectnessClosed : Bool
    quantumAdvantageClaimedFromTheseFixtures : Bool

canonicalClassicalOrderFindingBoundary : ClassicalOrderFindingBoundary
canonicalClassicalOrderFindingBoundary =
  classicalOrderFindingBoundary
    true true true true true true true false false false
