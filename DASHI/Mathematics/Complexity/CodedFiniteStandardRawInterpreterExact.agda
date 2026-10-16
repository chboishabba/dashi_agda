module DASHI.Mathematics.Complexity.CodedFiniteStandardRawInterpreterExact where

------------------------------------------------------------------------
-- EXECUTABLE UNIVERSAL SEMANTICS FOR THE UNTYPED SELF-DELIMITING MACHINE VIEW
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteStandardSelfDelimitingCodeExact as Code

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc right) = false
natEqual (suc left) zero = false
natEqual (suc left) (suc right) = natEqual left right

andBool : Bool → Bool → Bool
andBool false right = false
andBool true right = right

ruleKeyMatches : Code.RawRule → Nat → Nat → Bool
ruleKeyMatches rule state symbol =
  andBool
    (natEqual (Code.source rule) state)
    (natEqual (Code.read rule) symbol)

fetchRawRule :
  List Code.RawRule → Nat → Nat → Maybe Code.RawRule
fetchRawRule [] state symbol = nothing
fetchRawRule (rule ∷ rest) state symbol
  with ruleKeyMatches rule state symbol
... | true = just rule
... | false = fetchRawRule rest state symbol

record RawConfiguration : Set where
  constructor raw-configuration
  field
    left : List Nat
    state : Nat
    scanned : Nat
    right : List Nat

open RawConfiguration public

applyMoveRight :
  Code.RawMachine → List Nat → List Nat → Code.RawRule →
  Maybe RawConfiguration
applyMoveRight machine left [] rule =
  just
    (raw-configuration
      (Code.write rule ∷ left)
      (Code.target rule)
      (Code.blank machine)
      [])
applyMoveRight machine left (next ∷ rest) rule =
  just
    (raw-configuration
      (Code.write rule ∷ left)
      (Code.target rule)
      next
      rest)

applyRawRule :
  Code.RawMachine →
  RawConfiguration →
  Code.RawRule →
  Maybe RawConfiguration
applyRawRule machine (raw-configuration [] q a right) rule
  with Code.direction rule
... | zero =
      just
        (raw-configuration
          []
          (Code.target rule)
          (Code.blank machine)
          (Code.write rule ∷ right))
... | suc zero =
      just
        (raw-configuration
          []
          (Code.target rule)
          (Code.write rule)
          right)
... | suc (suc zero) =
      applyMoveRight machine [] right rule
... | suc (suc (suc invalid)) = nothing
applyRawRule machine (raw-configuration (near ∷ left) q a right) rule
  with Code.direction rule
... | zero =
      just
        (raw-configuration
          left
          (Code.target rule)
          near
          (Code.write rule ∷ right))
... | suc zero =
      just
        (raw-configuration
          (near ∷ left)
          (Code.target rule)
          (Code.write rule)
          right)
... | suc (suc zero) =
      applyMoveRight machine (near ∷ left) right rule
... | suc (suc (suc invalid)) = nothing

rawNext : Code.RawMachine → RawConfiguration → Maybe RawConfiguration
rawNext machine configuration
  with fetchRawRule
    (Code.rules machine)
    (state configuration)
    (scanned configuration)
... | nothing = nothing
... | just rule = applyRawRule machine configuration rule

iterateRaw :
  Nat → Code.RawMachine → RawConfiguration → Maybe RawConfiguration
iterateRaw zero machine configuration = just configuration
iterateRaw (suc steps) machine configuration
  with rawNext machine configuration
... | nothing = nothing
... | just next = iterateRaw steps machine next

runSelfDelimitedCode :
  Nat →
  List Bool →
  RawConfiguration →
  Maybe RawConfiguration
runSelfDelimitedCode steps bits initial
  with Code.decodeMachine bits
... | nothing = nothing
... | just (machine , suffix) =
      iterateRaw steps machine initial

runActualCodeReducesToRawView :
  (steps : Nat)
  (code : Coded.CodedFiniteStandardTM)
  (initial : RawConfiguration) →
  runSelfDelimitedCode
    steps
    (Code.selfDelimitingMachineCode code)
    initial
  ≡
  iterateRaw steps (Code.rawMachineView code) initial
runActualCodeReducesToRawView steps code initial
  rewrite Code.selfDelimitingRoundTrip code = refl

------------------------------------------------------------------------
-- MAX-CUT CONSEQUENCE
--
-- The universal-interpreter route now has an executable first-order semantic
-- kernel over self-delimiting machine code: parse, first-match dispatch, tape
-- update and bounded iteration. Remaining payments are typed-standard fidelity
-- on actual codes and compilation of this fixed recursion into one literal TM.
------------------------------------------------------------------------
