module DASHI.ComputerScience.HelloWorldFibreExact where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.ComputerScience.FibreMachineFoundation369Exact as CS

------------------------------------------------------------------------
-- HELLO WORLD: FIRST CLOSED EXECUTABLE FIBRE
--
-- This is intentionally below C/Rust/assembly and above any ASIC/FPGA/physical
-- realization.  It closes the smallest end-to-end ladder:
--
--   declared outcome -> abstract program -> execution -> observation -> cost.
--
-- Later language, compiler, machine-code, FPGA, ASIC, and physical fibres must
-- refine this semantic object relative to the consumer being paid; they are
-- not definitionally identified with it.
------------------------------------------------------------------------

data Message : Set where
  helloWorld : Message

data Instruction : Set where
  emit : Message → Instruction

Program : Set
Program = List Instruction

Output : Set
Output = List Message

execute : Program → Output
execute [] = []
execute (emit message ∷ program) = message ∷ execute program

stepCost : Program → Nat
stepCost [] = 0
stepCost (_ ∷ program) = suc (stepCost program)

helloWorldSpec : Output
helloWorldSpec = helloWorld ∷ []

helloWorldProgram : Program
helloWorldProgram = emit helloWorld ∷ []

helloWorldExecutesExactly :
  execute helloWorldProgram ≡ helloWorldSpec
helloWorldExecutesExactly = refl

helloWorldStepCostIsOne :
  stepCost helloWorldProgram ≡ 1
helloWorldStepCostIsOne = refl

------------------------------------------------------------------------
-- Fibre view.
--
-- State is the hidden abstract program.  Surface/outcome are executed output.
-- Cost is tracked separately, so extensional output equality does not silently
-- imply equal execution cost.
------------------------------------------------------------------------

helloWorldExecutionFibre : CS.ExecutionFibre
helloWorldExecutionFibre =
  CS.executionFibre
    Program
    Output
    Output
    Nat
    execute
    execute
    stepCost

helloWorldOutputIsConsumerAdequate :
  CS.ConsumerAdequate helloWorldExecutionFibre
helloWorldOutputIsConsumerAdequate =
  Descent.consumerObserverIsSufficient execute

record HelloWorldReceipt : Set where
  constructor helloWorldReceipt
  field
    program : Program
    observed : Output
    cost : Nat
    outputExact : observed ≡ helloWorldSpec
    costExact : cost ≡ 1

canonicalHelloWorldReceipt : HelloWorldReceipt
canonicalHelloWorldReceipt =
  helloWorldReceipt
    helloWorldProgram
    (execute helloWorldProgram)
    (stepCost helloWorldProgram)
    helloWorldExecutesExactly
    helloWorldStepCostIsOne

record HelloWorldBoundary : Set where
  constructor helloWorldBoundary
  field
    semanticsClosedBeforeLanguageChoice : Bool
    outputAndCostAreSeparateCoordinates : Bool
    ASICOrFPGARequiredForAbstractCorrectness : Bool
    compilerCorrectnessAlreadyClaimed : Bool

canonicalHelloWorldBoundary : HelloWorldBoundary
canonicalHelloWorldBoundary =
  helloWorldBoundary true true false false
