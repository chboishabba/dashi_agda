module DASHI.Mathematics.Complexity.CodedFiniteStandardSelfDelimitingCodeExact where

------------------------------------------------------------------------
-- SELF-DELIMITING GODEL CODE FOR CODED FINITE STANDARD MACHINES
--
-- The older static code is fixed-width relative to a machine whose state/symbol
-- widths are already known.  Runtime self-specialization needs a quote that can
-- be parsed without that external shape.  This owner adds a minimal unary-
-- framed representation of the same literal finite machine data.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (_×_; _,_)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded

------------------------------------------------------------------------
-- Basic list utilities.
------------------------------------------------------------------------

append : ∀ {A : Set} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

------------------------------------------------------------------------
-- Self-delimiting natural: n copies of true followed by false.
------------------------------------------------------------------------

encodeNat : Nat → List Bool
encodeNat zero = false ∷ []
encodeNat (suc n) = true ∷ encodeNat n

decodeNat : List Bool → Maybe (Nat × List Bool)
decodeNat [] = nothing
decodeNat (false ∷ rest) = just (zero , rest)
decodeNat (true ∷ rest) with decodeNat rest
... | nothing = nothing
... | just (value , suffix) = just (suc value , suffix)

decodeNatAppend :
  (value : Nat) (suffix : List Bool) →
  decodeNat (append (encodeNat value) suffix)
  ≡ just (value , suffix)
decodeNatAppend zero suffix = refl
decodeNatAppend (suc value) suffix
  rewrite decodeNatAppend value suffix = refl

------------------------------------------------------------------------
-- Untyped finite rule/machine syntax.
------------------------------------------------------------------------

record RawRule : Set where
  constructor raw-rule
  field
    source : Nat
    read : Nat
    target : Nat
    write : Nat
    direction : Nat

open RawRule public

record RawMachine : Set where
  constructor raw-machine
  field
    stateCount : Nat
    symbolCount : Nat
    blank : Nat
    initial : Nat
    accepting : Nat
    rules : List RawRule

open RawMachine public

directionCode : Local.Direction → Nat
directionCode Local.moveLeft = zero
directionCode Local.stayPut = suc zero
directionCode Local.moveRight = suc (suc zero)

rawRule :
  ∀ {states symbols : Nat} →
  Local.TapeRule (Fin.Fin states) (Fin.Fin symbols) → RawRule
rawRule rule = raw-rule
  (Fin.toℕ (Local.sourceState rule))
  (Fin.toℕ (Local.readSymbol rule))
  (Fin.toℕ (Local.targetState rule))
  (Fin.toℕ (Local.writeSymbol rule))
  (directionCode (Local.direction rule))

rawRules :
  ∀ {states symbols : Nat} →
  List (Local.TapeRule (Fin.Fin states) (Fin.Fin symbols)) →
  List RawRule
rawRules [] = []
rawRules (rule ∷ rest) = rawRule rule ∷ rawRules rest

rawMachineView : Coded.CodedFiniteStandardTM → RawMachine
rawMachineView code = raw-machine
  (Coded.stateCount code)
  (Coded.symbolCount code)
  (Fin.toℕ (Coded.blank code))
  (Fin.toℕ (Coded.initialState code))
  (Fin.toℕ (Coded.acceptingState code))
  (rawRules (Coded.rules code))

------------------------------------------------------------------------
-- Rule codec.
------------------------------------------------------------------------

encodeRule : RawRule → List Bool
encodeRule rule =
  append (encodeNat (source rule))
    (append (encodeNat (read rule))
      (append (encodeNat (target rule))
        (append (encodeNat (write rule))
          (encodeNat (direction rule)))))

decodeRule : List Bool → Maybe (RawRule × List Bool)
decodeRule bits with decodeNat bits
... | nothing = nothing
... | just (source , afterSource) with decodeNat afterSource
...   | nothing = nothing
...   | just (read , afterRead) with decodeNat afterRead
...     | nothing = nothing
...     | just (target , afterTarget) with decodeNat afterTarget
...       | nothing = nothing
...       | just (write , afterWrite) with decodeNat afterWrite
...         | nothing = nothing
...         | just (direction , suffix) =
              just (raw-rule source read target write direction , suffix)

decodeRuleAppend :
  (rule : RawRule) (suffix : List Bool) →
  decodeRule (append (encodeRule rule) suffix)
  ≡ just (rule , suffix)
decodeRuleAppend (raw-rule source read target write direction) suffix
  rewrite decodeNatAppend source
      (append (encodeNat read)
        (append (encodeNat target)
          (append (encodeNat write)
            (append (encodeNat direction) suffix))))
        | decodeNatAppend read
            (append (encodeNat target)
              (append (encodeNat write)
                (append (encodeNat direction) suffix)))
        | decodeNatAppend target
            (append (encodeNat write)
              (append (encodeNat direction) suffix))
        | decodeNatAppend write
            (append (encodeNat direction) suffix)
        | decodeNatAppend direction suffix = refl

------------------------------------------------------------------------
-- Fixed-count rule-list codec; the count is carried in the machine header.
------------------------------------------------------------------------

encodeRules : List RawRule → List Bool
encodeRules [] = []
encodeRules (rule ∷ rest) = append (encodeRule rule) (encodeRules rest)

decodeRules : Nat → List Bool → Maybe (List RawRule × List Bool)
decodeRules zero bits = just ([] , bits)
decodeRules (suc count) bits with decodeRule bits
... | nothing = nothing
... | just (rule , afterRule) with decodeRules count afterRule
...   | nothing = nothing
...   | just (rest , suffix) = just (rule ∷ rest , suffix)

decodeRulesAppend :
  (rules : List RawRule) (suffix : List Bool) →
  decodeRules
    (listLength rules)
    (append (encodeRules rules) suffix)
  ≡ just (rules , suffix)
decodeRulesAppend [] suffix = refl
decodeRulesAppend (rule ∷ rest) suffix
  rewrite decodeRuleAppend rule (append (encodeRules rest) suffix)
        | decodeRulesAppend rest suffix = refl

------------------------------------------------------------------------
-- Machine codec.  Header is completely self-framing.
------------------------------------------------------------------------

encodeMachine : RawMachine → List Bool
encodeMachine machine =
  append (encodeNat (stateCount machine))
    (append (encodeNat (symbolCount machine))
      (append (encodeNat (blank machine))
        (append (encodeNat (initial machine))
          (append (encodeNat (accepting machine))
            (append (encodeNat (listLength (rules machine)))
              (encodeRules (rules machine)))))))

decodeMachine : List Bool → Maybe (RawMachine × List Bool)
decodeMachine bits with decodeNat bits
... | nothing = nothing
... | just (states , afterStates) with decodeNat afterStates
...   | nothing = nothing
...   | just (symbols , afterSymbols) with decodeNat afterSymbols
...     | nothing = nothing
...     | just (blank , afterBlank) with decodeNat afterBlank
...       | nothing = nothing
...       | just (initial , afterInitial) with decodeNat afterInitial
...         | nothing = nothing
...         | just (accepting , afterAccepting) with decodeNat afterAccepting
...           | nothing = nothing
...           | just (ruleCount , afterCount) with decodeRules ruleCount afterCount
...             | nothing = nothing
...             | just (rules , suffix) =
                  just
                    (raw-machine states symbols blank initial accepting rules , suffix)

decodeMachineAppend :
  (machine : RawMachine) (suffix : List Bool) →
  decodeMachine (append (encodeMachine machine) suffix)
  ≡ just (machine , suffix)
decodeMachineAppend
    (raw-machine states symbols blank initial accepting rules)
    suffix
  rewrite decodeNatAppend states
      (append (encodeNat symbols)
        (append (encodeNat blank)
          (append (encodeNat initial)
            (append (encodeNat accepting)
              (append (encodeNat (listLength rules))
                (append (encodeRules rules) suffix))))))
        | decodeNatAppend symbols
            (append (encodeNat blank)
              (append (encodeNat initial)
                (append (encodeNat accepting)
                  (append (encodeNat (listLength rules))
                    (append (encodeRules rules) suffix)))))
        | decodeNatAppend blank
            (append (encodeNat initial)
              (append (encodeNat accepting)
                (append (encodeNat (listLength rules))
                  (append (encodeRules rules) suffix))))
        | decodeNatAppend initial
            (append (encodeNat accepting)
              (append (encodeNat (listLength rules))
                (append (encodeRules rules) suffix)))
        | decodeNatAppend accepting
            (append (encodeNat (listLength rules))
              (append (encodeRules rules) suffix))
        | decodeNatAppend (listLength rules)
            (append (encodeRules rules) suffix)
        | decodeRulesAppend rules suffix = refl

selfDelimitingMachineCode :
  Coded.CodedFiniteStandardTM → List Bool
selfDelimitingMachineCode code =
  encodeMachine (rawMachineView code)

selfDelimitingRoundTrip :
  (code : Coded.CodedFiniteStandardTM) →
  decodeMachine (selfDelimitingMachineCode code)
  ≡ just (rawMachineView code , [])
selfDelimitingRoundTrip code =
  decodeMachineAppend (rawMachineView code) []

------------------------------------------------------------------------
-- MAX-CUT CONSEQUENCE
--
-- Runtime self-specialization no longer depends on externally supplied machine
-- widths/cardinalities merely to parse its quote.  The same coded standard-TM
-- data now has a prefix-decodable finite representation carrying its own state,
-- symbol and rule framing.  This is syntax only: validation back into dependent
-- Fin-indexed machine code and execution of arbitrary decoded syntax remain
-- separate obligations.
------------------------------------------------------------------------
