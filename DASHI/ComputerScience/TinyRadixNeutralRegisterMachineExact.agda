module DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- RADIX-NEUTRAL TINY REGISTER MACHINE
--
-- Instruction semantics operate on Nat words.  Binary, balanced ternary,
-- Jacquard, or later hardware carriers are representation fibres below this
-- machine rather than distinct instruction semantics.
------------------------------------------------------------------------

data Register : Set where
  r0 r1 r2 : Register

record RegisterFile : Set where
  constructor registerFile
  field
    reg0 reg1 reg2 : Nat

open RegisterFile public

readRegister : RegisterFile → Register → Nat
readRegister regs r0 = reg0 regs
readRegister regs r1 = reg1 regs
readRegister regs r2 = reg2 regs

writeRegister : RegisterFile → Register → Nat → RegisterFile
writeRegister regs r0 value = registerFile value (reg1 regs) (reg2 regs)
writeRegister regs r1 value = registerFile (reg0 regs) value (reg2 regs)
writeRegister regs r2 value = registerFile (reg0 regs) (reg1 regs) value

Address : Set
Address = Nat

Memory : Set
Memory = List Nat

lookupNat : Nat → List Nat → Nat
lookupNat zero [] = 0
lookupNat zero (x ∷ xs) = x
lookupNat (suc n) [] = 0
lookupNat (suc n) (x ∷ xs) = lookupNat n xs

updateNat : Nat → Nat → List Nat → List Nat
updateNat zero value [] = value ∷ []
updateNat zero value (x ∷ xs) = value ∷ xs
updateNat (suc n) value [] = 0 ∷ updateNat n value []
updateNat (suc n) value (x ∷ xs) = x ∷ updateNat n value xs

minus : Nat → Nat → Nat
minus n zero = n
minus zero (suc m) = zero
minus (suc n) (suc m) = minus n m

equalNat : Nat → Nat → Bool
equalNat zero zero = true
equalNat zero (suc n) = false
equalNat (suc n) zero = false
equalNat (suc n) (suc m) = equalNat n m

lessNat : Nat → Nat → Bool
lessNat zero zero = false
lessNat zero (suc n) = true
lessNat (suc n) zero = false
lessNat (suc n) (suc m) = lessNat n m

data Instruction : Set where
  loadImmediate : Register → Nat → Instruction
  loadMemory : Register → Address → Instruction
  storeMemory : Register → Address → Instruction
  addRegister : Register → Register → Instruction
  subRegister : Register → Register → Instruction
  jumpIfZero : Register → Address → Instruction
  jumpIfEqual : Register → Register → Address → Instruction
  jumpIfLess : Register → Register → Address → Instruction
  jump : Address → Instruction
  outputRegister : Register → Instruction
  halt : Instruction

Program : Set
Program = List Instruction

fetchInstruction : Program → Nat → Instruction
fetchInstruction [] pc = halt
fetchInstruction (i ∷ is) zero = i
fetchInstruction (i ∷ is) (suc pc) = fetchInstruction is pc

record MachineState : Set where
  constructor machineState
  field
    pc : Nat
    program : Program
    memory : Memory
    registers : RegisterFile
    output : List Nat
    halted : Bool
    cycles : Nat

open MachineState public

appendNat : List Nat → Nat → List Nat
appendNat [] x = x ∷ []
appendNat (y ∷ ys) x = y ∷ appendNat ys x

step : MachineState → MachineState
step state with halted state
... | true = state
... | false with fetchInstruction (program state) (pc state)
...   | loadImmediate reg value =
      machineState
        (suc (pc state))
        (program state)
        (memory state)
        (writeRegister (registers state) reg value)
        (output state)
        false
        (suc (cycles state))
...   | loadMemory reg address =
      machineState
        (suc (pc state))
        (program state)
        (memory state)
        (writeRegister (registers state) reg (lookupNat address (memory state)))
        (output state)
        false
        (suc (cycles state))
...   | storeMemory reg address =
      machineState
        (suc (pc state))
        (program state)
        (updateNat address (readRegister (registers state) reg) (memory state))
        (registers state)
        (output state)
        false
        (suc (cycles state))
...   | addRegister target source =
      machineState
        (suc (pc state))
        (program state)
        (memory state)
        (writeRegister
          (registers state)
          target
          (readRegister (registers state) target + readRegister (registers state) source))
        (output state)
        false
        (suc (cycles state))
...   | subRegister target source =
      machineState
        (suc (pc state))
        (program state)
        (memory state)
        (writeRegister
          (registers state)
          target
          (minus (readRegister (registers state) target) (readRegister (registers state) source)))
        (output state)
        false
        (suc (cycles state))
...   | jumpIfZero reg target with readRegister (registers state) reg
...     | zero =
        machineState target (program state) (memory state) (registers state)
          (output state) false (suc (cycles state))
...     | suc n =
        machineState (suc (pc state)) (program state) (memory state) (registers state)
          (output state) false (suc (cycles state))
...   | jumpIfEqual left right target with equalNat (readRegister (registers state) left) (readRegister (registers state) right)
...     | true =
        machineState target (program state) (memory state) (registers state)
          (output state) false (suc (cycles state))
...     | false =
        machineState (suc (pc state)) (program state) (memory state) (registers state)
          (output state) false (suc (cycles state))
...   | jumpIfLess left right target with lessNat (readRegister (registers state) left) (readRegister (registers state) right)
...     | true =
        machineState target (program state) (memory state) (registers state)
          (output state) false (suc (cycles state))
...     | false =
        machineState (suc (pc state)) (program state) (memory state) (registers state)
          (output state) false (suc (cycles state))
...   | jump target =
      machineState target (program state) (memory state) (registers state)
        (output state) false (suc (cycles state))
...   | outputRegister reg =
      machineState
        (suc (pc state))
        (program state)
        (memory state)
        (registers state)
        (appendNat (output state) (readRegister (registers state) reg))
        false
        (suc (cycles state))
...   | halt =
      machineState
        (pc state)
        (program state)
        (memory state)
        (registers state)
        (output state)
        true
        (suc (cycles state))

runFuel : Nat → MachineState → MachineState
runFuel zero state = state
runFuel (suc fuel) state = runFuel fuel (step state)

------------------------------------------------------------------------
-- COUNTDOWN: first nontrivial control-flow fixture.
--
-- r0 = input n
-- r1 = constant 1
--
-- 0: JZ  r0 4
-- 1: OUT r0
-- 2: SUB r0 r1
-- 3: JMP 0
-- 4: HALT
------------------------------------------------------------------------

countdownProgram : Program
countdownProgram =
  jumpIfZero r0 4
  ∷ outputRegister r0
  ∷ subRegister r0 r1
  ∷ jump 0
  ∷ halt
  ∷ []

countdownInitialState : Nat → MachineState
countdownInitialState n =
  machineState 0 countdownProgram [] (registerFile n 1 0) [] false 0

countdownFuel : Nat → Nat
countdownFuel n = 4 * n + 2

countdownFinal : Nat → MachineState
countdownFinal n = runFuel (countdownFuel n) (countdownInitialState n)

countdownZeroOutput : output (countdownFinal 0) ≡ []
countdownZeroOutput = refl

countdownZeroCycles : cycles (countdownFinal 0) ≡ 2
countdownZeroCycles = refl

countdownZeroHalts : halted (countdownFinal 0) ≡ true
countdownZeroHalts = refl

countdownOneOutput : output (countdownFinal 1) ≡ 1 ∷ []
countdownOneOutput = refl

countdownOneCycles : cycles (countdownFinal 1) ≡ 6
countdownOneCycles = refl

countdownOneHalts : halted (countdownFinal 1) ≡ true
countdownOneHalts = refl

countdownThreeOutput : output (countdownFinal 3) ≡ 3 ∷ 2 ∷ 1 ∷ []
countdownThreeOutput = refl

countdownThreeCycles : cycles (countdownFinal 3) ≡ 14
countdownThreeCycles = refl

countdownThreeHalts : halted (countdownFinal 3) ≡ true
countdownThreeHalts = refl

countdownThreeTerminalPC : pc (countdownFinal 3) ≡ 4
countdownThreeTerminalPC = refl

countdownThreeTerminalR0 : reg0 (registers (countdownFinal 3)) ≡ 0
countdownThreeTerminalR0 = refl

------------------------------------------------------------------------
-- Exact instruction availability / semantic boundaries.
------------------------------------------------------------------------

record TinyMachineBoundary : Set where
  constructor tinyMachineBoundary
  field
    loadImmediatePresent : Bool
    loadPresent : Bool
    storePresent : Bool
    addPresent : Bool
    subtractPresent : Bool
    zeroBranchPresent : Bool
    equalityBranchPresent : Bool
    orderBranchPresent : Bool
    jumpPresent : Bool
    haltPresent : Bool
    outputPresent : Bool
    radixFixedByInstructionSemantics : Bool
    physicalTimingClaimed : Bool
    genericCountdownCostTheoremClosed : Bool

canonicalTinyMachineBoundary : TinyMachineBoundary
canonicalTinyMachineBoundary =
  tinyMachineBoundary
    true true true true true true true true true true true
    false false false
