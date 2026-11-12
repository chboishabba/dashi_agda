{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21NativeBitTapePhysicalMachineExact where

------------------------------------------------------------------------
-- F1 physical binary-tape substrate: FINITE LOCAL instructions.
--
-- One two-sided, one-head tape is represented by an explicit zipper.
-- Crossing either represented boundary creates exactly one blank cell.
-- A program instruction observes only its finite control state and
-- one symbol per tape, never the entire N21 source state. A separate\n-- TableProgram stores all finite transition entries explicitly. Each move
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
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
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

-- Literal, FINITELY STORED instructions, rather than an uncharged
-- higher-order transition oracle. Four choices are explicitly stored
-- for every observed tape cell; no list scan or Nat-valued decoding
-- is hidden in the transition itself.
record FourChoices (A : Set) : Set where
  constructor four
  field
    onB0 : A
    onB1 : A
    onBlank : A
    onMark : A
open FourChoices public

pickCell : {A : Set} → Cell → FourChoices A → A
pickCell B0 (four a b c d) = a
pickCell B1 (four a b c d) = b
pickCell Blank (four a b c d) = c
pickCell Mark (four a b c d) = d

-- A finite 4-ary table over k current work-tape symbols.
WorkTable : Nat → Set → Set
WorkTable zero A = A
WorkTable (suc k) A = FourChoices (WorkTable k A)

pickWork :
  {k : Nat} {A : Set} →
  Vec.Vec Cell k → WorkTable k A → A
pickWork Vec.[] entry = entry
pickWork (cell Vec.∷ heads) entry =
  pickWork heads (pickCell cell entry)

-- The finite-control dimension is also an actual vector of entries.
-- For fixed q and k this is a finite, fully enumerated transition
-- table of q * 4^(k+1) instruction entries.
record TableProgram (q k : Nat) : Set where
  constructor tableProgram
  field
    entries : Vec.Vec
      (FourChoices (WorkTable k (Instruction q k))) q
open TableProgram public

tableInstruction :
  {q k : Nat} →
  TableProgram q k →
  Fin.Fin q → Cell → Vec.Vec Cell k → Instruction q k
tableInstruction (tableProgram table) state input work =
  pickWork work (pickCell input (Vec.lookup table state))

-- Adapt a LITERAL finite table to the generic execution equations.
-- Kernel checking this source is distinct from proving that the
-- original N21 arithmetic/parser/history/threshold routines admit
-- a polynomial-cost compilation into such table instructions.
useLiteralTable :
  {q k : Nat} →
  TableProgram q k → LocalProgram q k
useLiteralTable table =
  record { localInstruction = tableInstruction table }


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

------------------------------------------------------------------------
-- F1/F2 physical TAPE footprint accounting for any fixed tape count.
-- This is the sum of represented head/left/right cells, not a bound
-- on source-language heap objects, sharing, stack or N21 compiler.
------------------------------------------------------------------------

workCellCount : {k : Nat} → Vec.Vec Tape k → Nat
workCellCount Vec.[] = zero
workCellCount (t Vec.∷ ts) = cellCount t + workCellCount ts

configurationCells :
  {q k : Nat} → Configuration q k → Nat
configurationCells (config state source work halted) =
  cellCount source + workCellCount work

-- Reassociation of the exact one-new-cell-per-tape charge.
cellBudgetRearrange :
  (a b k : Nat) →
  suc a + (b + k) ≡ (a + b) + suc k
cellBudgetRearrange a b k =
  Relation.Binary.PropositionalEquality.trans
    (cong suc (sym (NatP.+-assoc a b k)))
    (sym (NatP.+-suc (a + b) k))

allWorkTapesCellBudget :
  {k : Nat} (writes : Vec.Vec Cell k)
  (moves : Vec.Vec Direction k)
  (work : Vec.Vec Tape k) →
  workCellCount (applyWorkInstructions writes moves work)
    ≤ workCellCount work + k
allWorkTapesCellBudget {zero} Vec.[] Vec.[] Vec.[] =
  NatP.≤-refl
allWorkTapesCellBudget {suc k}
  (c Vec.∷ writes) (direction Vec.∷ moves) (t Vec.∷ work) =
  NatP.≤-trans
    (NatP.+-mono-≤
      (writeAndWalkCellBudget c direction t)
      (allWorkTapesCellBudget writes moves work))
    (NatP.≤-reflexive
      (cellBudgetRearrange
        (cellCount t) (workCellCount work) k))

-- Actual local instruction application to k work tapes plus ONE input
-- tape; upper bound: at most k+1 extra represented tape cells.
machineStepCellBudget :
  {q k : Nat} (program : LocalProgram q k)
  (cfg : Configuration q k) →
  configurationCells (machineStep program cfg)
    ≤ configurationCells cfg + suc k
machineStepCellBudget {q} {k} program (config state source work true) =
  NatP.m≤m+n
    (configurationCells (config state source work true)) (suc k)
machineStepCellBudget {q} {k} program (config state source work false)
  with localInstruction program state (atHead source) (readWorkHeads work)
... | instruction next symbol direction writes moves stop =
  NatP.≤-trans
    (NatP.+-mono-≤
      (writeAndWalkCellBudget symbol direction source)
      (allWorkTapesCellBudget writes moves work))
    (NatP.≤-reflexive
      (cellBudgetRearrange
        (cellCount source) (workCellCount work) k))

-- A concrete fuel-bounded physical-run footprint theorem.
-- Fuel counts literal local tape instructions, NOT original N21
-- source steps. This is deliberately NOT a polynomial verifier-clock
-- receipt, because a compiler and its instruction bound are missing.
machineRunCellBudget :
  {q k : Nat} (fuel : Nat) (program : LocalProgram q k)
  (cfg : Configuration q k) →
  configurationCells (machineRun fuel program cfg)
    ≤ configurationCells cfg + fuel * suc k
machineRunCellBudget {q} {k} zero program cfg =
  NatP.m≤m+n (configurationCells cfg) zero
machineRunCellBudget {q} {k} (suc fuel) program cfg =
  NatP.≤-trans
    (machineRunCellBudget fuel program (machineStep program cfg))
    (NatP.≤-trans
      (NatP.+-mono-≤
        (machineStepCellBudget program cfg)
        NatP.≤-refl)
      (NatP.≤-reflexive
        (NatP.+-assoc
          (configurationCells cfg) (suc k)
          (fuel * suc k))))
