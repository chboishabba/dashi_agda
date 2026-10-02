module DASHI.Mathematics.Complexity.PNotEqualsNPFiniteRuleTableMachineExact where

------------------------------------------------------------------------
-- FINITE RULE-TABLE SINGLE-TAPE MACHINE
--
-- This owner closes a real expressivity gap in the earlier finite
-- instruction calibration.  A standard tape transition depends jointly on
-- the current finite control state and the symbol being read.  The earlier
-- write/move/goto language had no conditional dispatch instruction.
--
-- Here a program is literally a FINITE list of rules
--
--   (source state, read bit) -> (write bit, move, target state)
--
-- scanned sequentially.  First-match semantics makes execution deterministic
-- even if the supplied list contains duplicate keys.  Every scan comparison
-- is charged explicitly.
--
-- This is a concrete operational single-tape model and an exact adapter into
-- the repository's abstract DeterministicMachine carrier.  The converse
-- compilation from every machine notion used by the Clay-facing complexity
-- layer remains a separate theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.DeterministicNondeterministicMachineExact as Machine

------------------------------------------------------------------------
-- Decidable key equality, kept executable and local.
------------------------------------------------------------------------

natEq : Nat → Nat → Bool
natEq zero zero = true
natEq zero (suc n) = false
natEq (suc m) zero = false
natEq (suc m) (suc n) = natEq m n

boolEq : Bool → Bool → Bool
boolEq false false = true
boolEq false true = false
boolEq true false = false
boolEq true true = true

andBool : Bool → Bool → Bool
andBool true b = b
andBool false b = false

------------------------------------------------------------------------
-- Literal standard transition table.
------------------------------------------------------------------------

data HeadMove : Set where
  moveL stay moveR : HeadMove

record TapeRule : Set where
  constructor rule
  field
    sourceState : Nat
    readBit : Bool
    writeBit : Bool
    headMove : HeadMove
    targetState : Nat

open TapeRule public

ruleMatches : Nat → Bool → TapeRule → Bool
ruleMatches q bit r =
  andBool (natEq q (sourceState r)) (boolEq bit (readBit r))

findRule : Nat → Bool → List TapeRule → Maybe TapeRule
findRule q bit [] = nothing
findRule q bit (r ∷ rs) with ruleMatches q bit r
... | true = just r
... | false = findRule q bit rs

ruleLookupComparisons : Nat → Bool → List TapeRule → Nat
ruleLookupComparisons q bit [] = suc zero
ruleLookupComparisons q bit (r ∷ rs) with ruleMatches q bit r
... | true = suc zero
... | false = suc (ruleLookupComparisons q bit rs)

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

ruleLookupComparisonsBound :
  (q : Nat) → (bit : Bool) → (program : List TapeRule) →
  ruleLookupComparisons q bit program ≤ suc (listLength program)
ruleLookupComparisonsBound q bit [] = s≤s z≤n
ruleLookupComparisonsBound q bit (r ∷ rs) with ruleMatches q bit r
... | true = s≤s z≤n
... | false = s≤s (ruleLookupComparisonsBound q bit rs)

------------------------------------------------------------------------
-- Literal bi-infinite tape represented by finite visited stacks.
-- Unvisited cells are blank=false.
------------------------------------------------------------------------

record RuleTapeConfiguration : Set where
  constructor config
  field
    leftCells : List Bool
    currentCell : Bool
    rightCells : List Bool
    controlState : Nat

open RuleTapeConfiguration public

writeCurrent : Bool → RuleTapeConfiguration → RuleTapeConfiguration
writeCurrent b c =
  config (leftCells c) b (rightCells c) (controlState c)

setState : Nat → RuleTapeConfiguration → RuleTapeConfiguration
setState q c =
  config (leftCells c) (currentCell c) (rightCells c) q

moveHead : HeadMove → RuleTapeConfiguration → RuleTapeConfiguration
moveHead stay c = c
moveHead moveL c with leftCells c
... | [] =
  config [] false (currentCell c ∷ rightCells c) (controlState c)
... | b ∷ bs =
  config bs b (currentCell c ∷ rightCells c) (controlState c)
moveHead moveR c with rightCells c
... | [] =
  config (currentCell c ∷ leftCells c) false [] (controlState c)
... | b ∷ bs =
  config (currentCell c ∷ leftCells c) b bs (controlState c)

applyRule : TapeRule → RuleTapeConfiguration → RuleTapeConfiguration
applyRule r c =
  setState (targetState r)
    (moveHead (headMove r)
      (writeCurrent (writeBit r) c))

ruleTableStep :
  List TapeRule → RuleTapeConfiguration → Maybe RuleTapeConfiguration
ruleTableStep program c with
  findRule (controlState c) (currentCell c) program
... | nothing = nothing
... | just r = just (applyRule r c)

------------------------------------------------------------------------
-- Operational work: one execution unit plus sequential rule-table scan.
------------------------------------------------------------------------

ruleTableStepWork :
  List TapeRule → RuleTapeConfiguration → Nat
ruleTableStepWork program c =
  suc (ruleLookupComparisons
    (controlState c) (currentCell c) program)

perStepRuleTableBudget : List TapeRule → Nat
perStepRuleTableBudget program =
  suc (suc (listLength program))

ruleTableStepWorkBound :
  (program : List TapeRule) →
  (c : RuleTapeConfiguration) →
  ruleTableStepWork program c ≤ perStepRuleTableBudget program
ruleTableStepWorkBound program c =
  s≤s
    (ruleLookupComparisonsBound
      (controlState c) (currentCell c) program)

runRuleTableWork :
  List TapeRule → Nat → RuleTapeConfiguration → Nat
runRuleTableWork program zero c = zero
runRuleTableWork program (suc n) c with ruleTableStep program c
... | nothing = ruleTableStepWork program c
... | just c' =
  ruleTableStepWork program c + runRuleTableWork program n c'

linearRuleTableBudget :
  List TapeRule → Nat → Nat
linearRuleTableBudget program zero = zero
linearRuleTableBudget program (suc n) =
  perStepRuleTableBudget program + linearRuleTableBudget program n

runRuleTableWorkLinearBound :
  (program : List TapeRule) →
  (steps : Nat) →
  (c : RuleTapeConfiguration) →
  runRuleTableWork program steps c ≤ linearRuleTableBudget program steps
runRuleTableWorkLinearBound program zero c = z≤n
runRuleTableWorkLinearBound program (suc n) c with ruleTableStep program c
... | nothing =
  NatP.≤-trans
    (ruleTableStepWorkBound program c)
    (NatP.m≤m+n
      (perStepRuleTableBudget program)
      (linearRuleTableBudget program n))
... | just c' =
  NatP.+-mono-≤
    (ruleTableStepWorkBound program c)
    (runRuleTableWorkLinearBound program n c')

------------------------------------------------------------------------
-- Exact adapter into the existing abstract deterministic-machine carrier.
-- Halting is "no matching rule"; acceptance remains a supplied predicate on
-- the concrete final configuration.
------------------------------------------------------------------------

record FiniteRuleTapeProgram : Set₁ where
  field
    Input : Set
    rules : List TapeRule
    initial : Input → RuleTapeConfiguration
    accepting : RuleTapeConfiguration → Set

open FiniteRuleTapeProgram public

ruleTableDeterministicMachine :
  FiniteRuleTapeProgram → Machine.DeterministicMachine
ruleTableDeterministicMachine P = record
  { Machine.dInput = Input P
  ; Machine.dConfiguration = RuleTapeConfiguration
  ; Machine.dInitial = initial P
  ; Machine.dNext = ruleTableStep (rules P)
  ; Machine.dAccepting = accepting P
  }

ruleTableAdapterStepExact :
  (P : FiniteRuleTapeProgram) →
  (c : RuleTapeConfiguration) →
  Machine.dNext (ruleTableDeterministicMachine P) c
    ≡ ruleTableStep (rules P) c
ruleTableAdapterStepExact P c = refl

------------------------------------------------------------------------
-- Executable regression: state 0 reading blank writes true, moves right,
-- and enters state 1; no rule is supplied for state 1, so the next step
-- halts.
------------------------------------------------------------------------

testRule : TapeRule
testRule = rule zero false true moveR (suc zero)

testProgram : List TapeRule
testProgram = testRule ∷ []

testInitial : RuleTapeConfiguration
testInitial = config [] false [] zero

testAfterOne : RuleTapeConfiguration
testAfterOne = config (true ∷ []) false [] (suc zero)

testFirstStep :
  ruleTableStep testProgram testInitial ≡ just testAfterOne
testFirstStep = refl

testSecondStep :
  ruleTableStep testProgram testAfterOne ≡ nothing
testSecondStep = refl

------------------------------------------------------------------------
-- MAX-CUT BOUNDARY
--
-- PAID:
-- * literal finite state+symbol transition table;
-- * deterministic executable dispatch by sequential finite scan;
-- * explicit O(|program|) per-step interpreter cost;
-- * linear-in-T run-work bound for fixed finite program;
-- * exact embedding into the repository DeterministicMachine semantics.
--
-- OPEN:
-- * encode arbitrary standard multi-tape/TM machines into this one-tape model
--   with a proved polynomial overhead;
-- * prove the reverse reasonable simulation needed for machine invariance;
-- * terminate Cook-Levin/SAT complexity in this exact operational cost model;
-- * discover the universal simulation-invariant SAT lower-bound obstruction.
------------------------------------------------------------------------
