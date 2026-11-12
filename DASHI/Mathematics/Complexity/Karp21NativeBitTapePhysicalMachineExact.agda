{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21NativeBitTapePhysicalMachineExact where

------------------------------------------------------------------------
-- F1 physical binary-tape substrate: FINITE LOCAL instructions.
--
-- One two-sided, one-head tape is represented by an explicit zipper.
-- Crossing either represented boundary creates exactly one blank cell.
-- A program instruction observes only its finite control state and
-- one symbol per tape, never the entire N21 source state. Each move
-- rewrites one symbol and moves its head by at most one cell.
--
-- The tape/transition system below is executable. Its elementary
-- one-head footprint inequalities are proved below; these are NOT
-- a compiler of the existing N21 parser/priority step, do NOT bound
-- all persistent heap allocations, and do NOT prove PR.InNP.
-- F3 must supply an N21 instruction-level forward simulation and F4
-- must pay for parsing and all physical instructions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (length)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; sym; subst)
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word

data Cell : Set where
  B0 B1 Blank Mark : Cell

data Direction : Set where
  left right stay : Direction

record Tape : Set where
  constructor tape
  field
    leftOfHead : List Cell
    atHead     : Cell
    rightOfHead : List Cell
open Tape public

-- Both finite lists are closest-to-head first. There are implicit
-- blanks beyond the represented prefix on either side.
write : Cell → Tape → Tape
write value (tape ls old rs) = tape ls value rs

walk : Direction → Tape → Tape
walk stay t = t
walk left (tape [] c rs) = tape [] Blank (c ∷ rs)
walk left (tape (l ∷ ls) c rs) = tape ls l (c ∷ rs)
walk right (tape ls c []) = tape (c ∷ ls) Blank []
walk right (tape ls c (r ∷ rs)) = tape (c ∷ ls) r rs

cellCount : Tape → Nat
cellCount (tape ls c rs) = suc (length ls + length rs)

writePreservesCellCount :
  (symbol : Cell) (t : Tape) →
  cellCount (write symbol t) ≡ cellCount t
writePreservesCellCount symbol (tape ls c rs) = refl

n≤sucN : (n : Nat) → n ≤ suc n
n≤sucN zero = z≤n
n≤sucN (suc n) = s≤s (n≤sucN n)

-- Exact selected zipper representation: every physical head movement
-- increases the number of represented cells by at most one, including
-- movement outside the currently represented span.
walkAddsAtMostOneCell :
  (direction : Direction) (t : Tape) →
  cellCount (walk direction t) ≤ suc (cellCount t)
walkAddsAtMostOneCell stay t = n≤sucN (cellCount t)
walkAddsAtMostOneCell left (tape [] c rs) = NatP.≤-refl
walkAddsAtMostOneCell left (tape (l ∷ ls) c rs) =
  NatP.≤-trans
    (NatP.≤-reflexive
      (cong suc (NatP.+-suc (length ls) (length rs))))
    (n≤sucN (cellCount (tape (l ∷ ls) c rs)))
walkAddsAtMostOneCell right (tape ls c []) = NatP.≤-refl
walkAddsAtMostOneCell right (tape ls c (r ∷ rs)) =
  NatP.≤-trans
    (NatP.≤-reflexive
      (cong suc (sym (NatP.+-suc (length ls) (length rs)))))
    (n≤sucN (cellCount (tape ls c (r ∷ rs))))

-- Writing a symbol never changes the zipper footprint. Consequently
-- one literal physical write-and-move instruction adds at most one
-- represented tape cell; no abstract high-level arithmetic is charged
-- as a constant-time instruction.
writeAndWalkCellBudget :
  (symbol : Cell) (direction : Direction) (t : Tape) →
  cellCount (walk direction (write symbol t)) ≤ suc (cellCount t)
writeAndWalkCellBudget symbol direction t =
  subst
    (λ n → cellCount (walk direction (write symbol t)) ≤ suc n)
    (writePreservesCellCount symbol t)
    (walkAddsAtMostOneCell direction (write symbol t))

-- The two inverse movement equations are about a head situated
-- INSIDE represented data, not boundary-created implicit blanks.
leftThenRightInterior :
  (l c : Cell) (ls rs : List Cell) →
  walk right (walk left (tape (l ∷ ls) c rs))
    ≡ tape (l ∷ ls) c rs
leftThenRightInterior l c ls rs = refl

rightThenLeftInterior :
  (r c : Cell) (ls rs : List Cell) →
  walk left (walk right (tape ls c (r ∷ rs)))
    ≡ tape ls c (r ∷ rs)
rightThenLeftInterior r c ls rs = refl

encodeBit : Bool → Cell
encodeBit false = B0
encodeBit true = B1

encodeBits : Word.BitWord → List Cell
encodeBits [] = []
encodeBits (bit ∷ bits) = encodeBit bit ∷ encodeBits bits

-- A literal source bit-word starts with its first symbol under the
-- input head. Empty input starts on Blank.
initialInputTape : Word.BitWord → Tape
initialInputTape [] = tape [] Blank []
initialInputTape (bit ∷ bits) =
  tape [] (encodeBit bit) (encodeBits bits)

blankTape : Tape
blankTape = tape [] Blank []

-- A finite multi-tape transition writes and moves each tape exactly
-- once. Unlike the attachment's one-char Instruction sketch, it
-- specifies an action for the input tape AND every work tape.
record Instruction (numberOfStates workTapeCount : Nat) : Set where
  constructor instruction
  field
    nextState : Fin.Fin numberOfStates
    inputWrite : Cell
    inputMove : Direction
    workWrites : Vec.Vec Cell workTapeCount
    workMoves : Vec.Vec Direction workTapeCount
    haltAfterStep : Bool
open Instruction public

record Configuration (numberOfStates workTapeCount : Nat) : Set where
  constructor config
  field
    control : Fin.Fin numberOfStates
    inputTape : Tape
    workTapes : Vec.Vec Tape workTapeCount
    halted : Bool
open Configuration public

readWorkHeads :
  {k : Nat} → Vec.Vec Tape k → Vec.Vec Cell k
readWorkHeads Vec.[] = Vec.[]
readWorkHeads (t Vec.∷ ts) =
  atHead t Vec.∷ readWorkHeads ts

applyWorkInstructions :
  {k : Nat} →
  Vec.Vec Cell k → Vec.Vec Direction k →
  Vec.Vec Tape k → Vec.Vec Tape k
applyWorkInstructions Vec.[] Vec.[] Vec.[] = Vec.[]
applyWorkInstructions (c Vec.∷ cs) (d Vec.∷ ds) (t Vec.∷ ts) =
  walk d (write c t) Vec.∷ applyWorkInstructions cs ds ts

-- The transition table sees a finite control state and k+1 current
-- symbols only. Instantiating this interface with a true finite table,
-- then compiling the original N21 verifier, is still a separate gate.
record LocalProgram (numberOfStates workTapeCount : Nat) : Set where
  field
    localInstruction :
      Fin.Fin numberOfStates →
      Cell →
      Vec.Vec Cell workTapeCount →
      Instruction numberOfStates workTapeCount
open LocalProgram public

machineStep :
  {q k : Nat} →
  LocalProgram q k → Configuration q k → Configuration q k
machineStep program (config state source work true) =
  config state source work true
machineStep program (config state source work false)
  with localInstruction program state (atHead source) (readWorkHeads work)
... | instruction next writeInput moveInput writes moves stop =
  config next
    (walk moveInput (write writeInput source))
    (applyWorkInstructions writes moves work)
    stop

machineRun :
  {q k : Nat} →
  Nat → LocalProgram q k → Configuration q k → Configuration q k
machineRun zero program state = state
machineRun (suc fuel) program state =
  machineRun fuel program (machineStep program state)

haltedMachineStepIsIdentity :
  {q k : Nat} (program : LocalProgram q k)
  (state : Fin.Fin q) (source : Tape)
  (work : Vec.Vec Tape k) →
  machineStep program (config state source work true)
    ≡ config state source work true
haltedMachineStepIsIdentity program state source work = refl
