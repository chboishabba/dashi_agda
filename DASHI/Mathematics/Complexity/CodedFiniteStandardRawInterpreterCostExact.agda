module DASHI.Mathematics.Complexity.CodedFiniteStandardRawInterpreterCostExact where

------------------------------------------------------------------------
-- EXPLICIT WORK ACCOUNTING FOR THE FIRST-ORDER RAW INTERPRETER
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.CodedFiniteStandardSelfDelimitingCodeExact as Code
import DASHI.Mathematics.Complexity.CodedFiniteStandardRawInterpreterExact as Raw

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

appendLength :
  ∀ {A : Set} (xs ys : List A) →
  listLength (Code.append xs ys) ≡ listLength xs + listLength ys
appendLength [] ys = refl
appendLength (x ∷ xs) ys rewrite appendLength xs ys = refl

encodeNatLength :
  (n : Nat) → listLength (Code.encodeNat n) ≡ suc n
encodeNatLength zero = refl
encodeNatLength (suc n) rewrite encodeNatLength n = refl

------------------------------------------------------------------------
-- Parser work: one unit per inspected bit.
------------------------------------------------------------------------

decodeNatWork : List Bool → Nat
decodeNatWork [] = zero
decodeNatWork (false ∷ rest) = suc zero
decodeNatWork (true ∷ rest) = suc (decodeNatWork rest)

decodeNatWorkBound :
  (bits : List Bool) → decodeNatWork bits ≤ listLength bits
decodeNatWorkBound [] = z≤n
decodeNatWorkBound (false ∷ rest) = s≤s z≤n
decodeNatWorkBound (true ∷ rest) = s≤s (decodeNatWorkBound rest)

decodeNatEncodedWork :
  (n : Nat) (suffix : List Bool) →
  decodeNatWork (Code.append (Code.encodeNat n) suffix) ≡ suc n
decodeNatEncodedWork zero suffix = refl
decodeNatEncodedWork (suc n) suffix
  rewrite decodeNatEncodedWork n suffix = refl

------------------------------------------------------------------------
-- First-match rule scan work.
------------------------------------------------------------------------

fetchRawRuleWork :
  List Code.RawRule → Nat → Nat → Nat
fetchRawRuleWork [] state symbol = zero
fetchRawRuleWork (rule ∷ rest) state symbol
  with Raw.ruleKeyMatches rule state symbol
... | true = suc zero
... | false = suc (fetchRawRuleWork rest state symbol)

fetchRawRuleWorkBound :
  (rules : List Code.RawRule)
  (state symbol : Nat) →
  fetchRawRuleWork rules state symbol ≤ listLength rules
fetchRawRuleWorkBound [] state symbol = z≤n
fetchRawRuleWorkBound (rule ∷ rest) state symbol
  with Raw.ruleKeyMatches rule state symbol
... | true = s≤s z≤n
... | false = s≤s (fetchRawRuleWorkBound rest state symbol)

------------------------------------------------------------------------
-- One simulated edge costs its table scan plus one tape-update unit.
------------------------------------------------------------------------

rawStepWork :
  Code.RawMachine → Raw.RawConfiguration → Nat
rawStepWork machine configuration =
  fetchRawRuleWork
    (Code.rules machine)
    (Raw.state configuration)
    (Raw.scanned configuration)
  + suc zero

rawStepWorkBound :
  (machine : Code.RawMachine)
  (configuration : Raw.RawConfiguration) →
  rawStepWork machine configuration
  ≤ suc (listLength (Code.rules machine))
rawStepWorkBound machine configuration =
  NatP.+-mono-≤
    (fetchRawRuleWorkBound
      (Code.rules machine)
      (Raw.state configuration)
      (Raw.scanned configuration))
    (NatP.≤-refl (suc zero))

------------------------------------------------------------------------
-- Accumulated semantic simulation work follows the same bounded iteration.
------------------------------------------------------------------------

iterateRawWork :
  Nat → Code.RawMachine → Raw.RawConfiguration → Nat
iterateRawWork zero machine configuration = zero
iterateRawWork (suc steps) machine configuration =
  rawStepWork machine configuration
  + nextWork
  where
    nextWork : Nat
    nextWork with Raw.rawNext machine configuration
    ... | nothing = zero
    ... | just next = iterateRawWork steps machine next

iterateRawWorkBound :
  (steps : Nat)
  (machine : Code.RawMachine)
  (configuration : Raw.RawConfiguration) →
  iterateRawWork steps machine configuration
  ≤ steps * suc (listLength (Code.rules machine))
iterateRawWorkBound zero machine configuration = z≤n
iterateRawWorkBound (suc steps) machine configuration
  with Raw.rawNext machine configuration
... | nothing =
  NatP.≤-trans
    (rawStepWorkBound machine configuration)
    (NatP.m≤m+n
      (suc (listLength (Code.rules machine)))
      (steps * suc (listLength (Code.rules machine))))
... | just next =
  NatP.≤-trans
    (NatP.+-mono-≤
      (rawStepWorkBound machine configuration)
      (iterateRawWorkBound steps machine next))
    (NatP.≤-refl
      (suc (listLength (Code.rules machine))
        + steps * suc (listLength (Code.rules machine))))

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The fixed raw universal semantics has an explicit linear-in-simulated-time
-- dispatch/update envelope: T simulated edges cost at most
--
--     T * (|rules| + 1).
--
-- Machine-code parsing is separately bit-linear.  A literal standard-TM U may
-- add head-routing/representation overhead, but no hidden super-polynomial
-- primitive remains in the semantic interpreter itself.
------------------------------------------------------------------------
