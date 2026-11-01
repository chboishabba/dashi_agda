module DASHI.Mathematics.Complexity.PNotEqualsNPFiniteTapeStutteringCalibrationExact where

------------------------------------------------------------------------
-- FINITE TAPE PROGRAM AND STUTTERING REGRESSION TEST
--
-- This model has an ACTUAL FINITE list of elementary instructions.
-- No instruction invokes an extensional SAT-decider or semantic oracle.
--
-- Tape : (reverse-left cells, current cell, right cells).
-- Instructions: write, move left, move right, jump, halt.
-- Fetch: scans a FINITE instruction list by the program counter.
--
-- One logical program step performs one instruction fetch plus one
-- constructor-based operation. The lookup comparisons are counted by the
-- same primitive recursion as fetch.
--
-- The existing stuttering transformation is applied to THIS concrete
-- machine, rather than to an extensional decision-function machine.
--
-- The result is a real finite-instruction calibration example, but not
-- yet a multi-tape Turing-machine universal simulator or SAT lower bound.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.Complexity.DeterministicNondeterministicMachineExact as Machine
import DASHI.Mathematics.Complexity.PNotEqualsNPActualMachineStutteringTransportExact as Stutter

------------------------------------------------------------------------
-- Finite machine instructions and a program counter.
------------------------------------------------------------------------

data TapeInstruction : Set where
  writeCell : Bool → TapeInstruction
  moveLeft moveRight : TapeInstruction
  goto : Nat → TapeInstruction
  stop : TapeInstruction

data ProgramCounter : Set where
  active : Nat → ProgramCounter
  halted : ProgramCounter

record TapeConfiguration : Set where
  constructor tape-configuration
  field
    leftCells : List Bool
    currentCell : Bool
    rightCells : List Bool
    counter : ProgramCounter

open TapeConfiguration public

------------------------------------------------------------------------
-- Concrete finite-code lookup, including explicit exhausted-code behavior.
------------------------------------------------------------------------

fetchInstruction : List TapeInstruction → Nat → TapeInstruction
fetchInstruction [] position = stop
fetchInstruction (instruction ∷ rest) zero = instruction
fetchInstruction (instruction ∷ rest) (suc position) =
  fetchInstruction rest position

fetchComparisons : List TapeInstruction → Nat → Nat
fetchComparisons [] position = suc zero
fetchComparisons (instruction ∷ rest) zero = suc zero
fetchComparisons (instruction ∷ rest) (suc position) =
  suc (fetchComparisons rest position)

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ rest) = suc (listLength rest)

------------------------------------------------------------------------
-- No hidden random-access code read: traversed instruction cells are counted.
------------------------------------------------------------------------

fetchComparisonsWithinCodeLength :
  (program : List TapeInstruction) →
  (position : Nat) →
  fetchComparisons program position ≤ suc (listLength program)
fetchComparisonsWithinCodeLength [] position = s≤s z≤n
fetchComparisonsWithinCodeLength (instruction ∷ rest) zero =
  s≤s z≤n
fetchComparisonsWithinCodeLength (instruction ∷ rest) (suc position) =
  s≤s (fetchComparisonsWithinCodeLength rest position)

------------------------------------------------------------------------
-- One elementary instruction changes at most one tape cell/stack endpoint
-- or one program counter. Empty tape space reads as blank=false.
-- Fetch one code instruction AND execute it on the literal tape carrier.
--
-- The instruction 'write' and both moves then advance the *existing* PC.
-- This separate owner never postulates a machine that produces the desired
-- final state in one opaque transition.
------------------------------------------------------------------------

executeFetched :
  Nat → TapeInstruction → TapeConfiguration → TapeConfiguration
executeFetched currentPC (writeCell bit) cfg =
  tape-configuration
    (leftCells cfg) bit (rightCells cfg) (active (suc currentPC))
executeFetched currentPC moveLeft cfg
    with leftCells cfg
... | [] =
  tape-configuration
    [] false (currentCell cfg ∷ rightCells cfg)
    (active (suc currentPC))
... | left ∷ rest =
  tape-configuration
    rest left (currentCell cfg ∷ rightCells cfg)
    (active (suc currentPC))
executeFetched currentPC moveRight cfg
    with rightCells cfg
... | [] =
  tape-configuration
    (currentCell cfg ∷ leftCells cfg)
    false [] (active (suc currentPC))
... | right ∷ rest =
  tape-configuration
    (currentCell cfg ∷ leftCells cfg)
    right rest (active (suc currentPC))
executeFetched currentPC (goto position) cfg =
  tape-configuration
    (leftCells cfg) (currentCell cfg) (rightCells cfg)
    (active position)
executeFetched currentPC stop cfg =
  tape-configuration
    (leftCells cfg) (currentCell cfg) (rightCells cfg)
    halted

tapeStep :
  List TapeInstruction →
  TapeConfiguration →
  Maybe TapeConfiguration
tapeStep program cfg with counter cfg
... | halted = nothing
... | active position =
  just (executeFetched position (fetchInstruction program position) cfg)

tapeStepWork :
  List TapeInstruction → TapeConfiguration → Nat
tapeStepWork program cfg with counter cfg
... | halted = zero
... | active position = suc (fetchComparisons program position)

------------------------------------------------------------------------
-- UNIVERSAL INTERPRETER COST: the program is DATA.
--
-- One interpreted active step pays one execution unit plus the sequential
-- code scan. Hence no program can hide an uncharged arbitrary semantic call.
------------------------------------------------------------------------

perStepInterpreterBudget :
  List TapeInstruction → Nat
perStepInterpreterBudget program =
  suc (suc (listLength program))

tapeStepWorkWithinProgramBudget :
  (program : List TapeInstruction) →
  (cfg : TapeConfiguration) →
  tapeStepWork program cfg ≤ perStepInterpreterBudget program
tapeStepWorkWithinProgramBudget program cfg with counter cfg
... | halted = z≤n
... | active position =
  s≤s (fetchComparisonsWithinCodeLength program position)

------------------------------------------------------------------------
-- Total work of at most 'steps' universal-interpreter transitions.
-- If execution halts early, the remaining requested steps cost zero.
------------------------------------------------------------------------

runInterpreterWork :
  List TapeInstruction →
  Nat →
  TapeConfiguration →
  Nat
runInterpreterWork program zero cfg = zero
runInterpreterWork program (suc steps) cfg with tapeStep program cfg
... | nothing =
  tapeStepWork program cfg
... | just next =
  tapeStepWork program cfg
  + runInterpreterWork program steps next

linearInterpreterBudget :
  List TapeInstruction → Nat → Nat
linearInterpreterBudget program zero = zero
linearInterpreterBudget program (suc steps) =
  perStepInterpreterBudget program
  + linearInterpreterBudget program steps

runInterpreterWorkLinearBound :
  (program : List TapeInstruction) →
  (steps : Nat) →
  (cfg : TapeConfiguration) →
  runInterpreterWork program steps cfg
  ≤ linearInterpreterBudget program steps
runInterpreterWorkLinearBound program zero cfg =
  z≤n
runInterpreterWorkLinearBound program (suc steps) cfg
    with tapeStep program cfg
... | nothing =
  NatP.≤-trans
    (tapeStepWorkWithinProgramBudget program cfg)
    (NatP.m≤m+n
      (perStepInterpreterBudget program)
      (linearInterpreterBudget program steps))
... | just next =
  NatP.+-mono-≤
    (tapeStepWorkWithinProgramBudget program cfg)
    (runInterpreterWorkLinearBound program steps next)

------------------------------------------------------------------------
-- A fixed finite program therefore has LINEAR universal-interpreter
-- overhead in the requested transition count. Any proposed lower-bound
-- invariant that explodes merely under this representation change is not
-- invariant under harmless finite-program interpretation.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Concrete machine instance: accepted only AFTER the finite STOP
-- instruction is EXECUTED and the current tape cell equals true.
------------------------------------------------------------------------

data EmptyInput : Set where
  emptyInput : EmptyInput

initialTape : TapeConfiguration
initialTape = tape-configuration [] false [] (active zero)

finiteTapeMachine :
  (program : List TapeInstruction) →
  Machine.DeterministicMachine
finiteTapeMachine program = record
  { Machine.dInput = EmptyInput
  ; Machine.dConfiguration = TapeConfiguration
  ; Machine.dInitial = λ _ → initialTape
  ; Machine.dNext = tapeStep program
  ; Machine.dAccepting = λ cfg →
      (counter cfg ≡ halted) × (currentCell cfg ≡ true)
  }

------------------------------------------------------------------------
-- Literal executable regression: WRITE(true); STOP.
-- The original interpreter reaches its accepting state in TWO operations.
-- Its stuttered version reaches the corresponding READY state in FOUR.
------------------------------------------------------------------------

testProgram : List TapeInstruction
testProgram = writeCell true ∷ stop ∷ []

testFinal : TapeConfiguration
testFinal = tape-configuration [] true [] halted

testTwoSteps :
  Machine.iterateDeterministic
    (finiteTapeMachine testProgram)
    (suc (suc zero))
    initialTape
  ≡ just testFinal
testTwoSteps = refl

testAccepted :
  Machine.dAccepting
    (finiteTapeMachine testProgram)
    testFinal
testAccepted = refl , refl

testFirstStepWork :
  tapeStepWork testProgram initialTape ≡ suc (suc zero)
testFirstStepWork = refl

testSecondStepWork :
  tapeStepWork testProgram
    (executeFetched zero (writeCell true) initialTape)
  ≡ suc (suc (suc zero))
testSecondStepWork = refl

testFourStutterSteps :
  Machine.iterateDeterministic
    (Stutter.stutteringMachine (finiteTapeMachine testProgram))
    (suc (suc (suc (suc zero))))
    (Stutter.ready initialTape)
  ≡
  just (Stutter.ready testFinal)
testFourStutterSteps =
  trans
    (Stutter.stutteringRunExact
      (finiteTapeMachine testProgram)
      (suc (suc zero))
      initialTape)
    (cong Stutter.readyMaybe testTwoSteps)

------------------------------------------------------------------------
-- BOUNDARY:
-- The two/four transition counts are exact in the listed-instruction
-- interpreter. The declared fetch work is 2+3 comparisons plus the actual
-- two executed tape operations; this model still requires a fixed encoding
-- and bit-level lookup cost to become a universal Turing-time statement.
------------------------------------------------------------------------
