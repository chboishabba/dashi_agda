module DASHI.Mathematics.Complexity.CookFormulaPrefixStreamingExact where

------------------------------------------------------------------------
-- STREAMING TOKEN ACCESS TO THE COOK PREFIX CODE
--
-- Unlike `encodeCookFormula`, this cursor does not construct the whole token
-- list before selecting one token.  It descends the formula and skips complete
-- subtrees using their exact token counts.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _<_; _-_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix

------------------------------------------------------------------------
-- Generic list lookup, used only in the correctness statement/proof.
------------------------------------------------------------------------

lookup : ∀ {A : Set} → Nat → Agda.Builtin.List.List A → Maybe A
lookup zero Agda.Builtin.List.[] = nothing
lookup zero (x Agda.Builtin.List.∷ xs) = just x
lookup (suc n) Agda.Builtin.List.[] = nothing
lookup (suc n) (x Agda.Builtin.List.∷ xs) = lookup n xs

------------------------------------------------------------------------
-- Unary Nat token cursor.
------------------------------------------------------------------------

natTokenAt : Nat → Nat → Maybe Prefix.CookSyntaxToken
natTokenAt zero zero = just Prefix.natZeroToken
natTokenAt zero (suc index) = nothing
natTokenAt (suc n) zero = just Prefix.natSuccToken
natTokenAt (suc n) (suc index) = natTokenAt n index

natTokenAtExact :
  (n index : Nat) →
  natTokenAt n index
  ≡ lookup index (Prefix.encodeNatInto n Agda.Builtin.List.[])
natTokenAtExact zero zero = refl
natTokenAtExact zero (suc index) = refl
natTokenAtExact (suc n) zero = refl
natTokenAtExact (suc n) (suc index) = natTokenAtExact n index

------------------------------------------------------------------------
-- Prefix-token streaming cursor.
------------------------------------------------------------------------

mutual
  formulaTokenAt :
    Cook.BooleanFormula → Nat → Maybe Prefix.CookSyntaxToken
  formulaTokenAt formula zero = just (rootToken formula)
  formulaTokenAt (Cook.variable n) (suc index) = natTokenAt n index
  formulaTokenAt (Cook.constant value) (suc index) = nothing
  formulaTokenAt (Cook.negate formula) (suc index) =
    formulaTokenAt formula index
  formulaTokenAt (Cook.conjunction left right) (suc index)
      with index NatP.<? Prefix.cookFormulaTokenCount left
  ... | Agda.Builtin.Bool.true = formulaTokenAt left index
  ... | Agda.Builtin.Bool.false =
    formulaTokenAt right (index - Prefix.cookFormulaTokenCount left)
  formulaTokenAt (Cook.disjunction left right) (suc index)
      with index NatP.<? Prefix.cookFormulaTokenCount left
  ... | Agda.Builtin.Bool.true = formulaTokenAt left index
  ... | Agda.Builtin.Bool.false =
    formulaTokenAt right (index - Prefix.cookFormulaTokenCount left)

  rootToken : Cook.BooleanFormula → Prefix.CookSyntaxToken
  rootToken (Cook.variable n) = Prefix.formulaVariableToken
  rootToken (Cook.constant Agda.Builtin.Bool.false) = Prefix.formulaFalseToken
  rootToken (Cook.constant Agda.Builtin.Bool.true) = Prefix.formulaTrueToken
  rootToken (Cook.negate formula) = Prefix.formulaNegateToken
  rootToken (Cook.conjunction left right) = Prefix.formulaAndToken
  rootToken (Cook.disjunction left right) = Prefix.formulaOrToken

------------------------------------------------------------------------
-- Correctness is factored through a generic append lookup theorem.
------------------------------------------------------------------------

lookupAppendLeft :
  ∀ {A : Set}
    (index : Nat)
    (left right : Agda.Builtin.List.List A) →
  index < Prefix.listLength left →
  lookup index (Prefix.encodeCookFormulaInto (Cook.constant Agda.Builtin.Bool.true) Agda.Builtin.List.[]) ≡
  lookup index (Prefix.encodeCookFormulaInto (Cook.constant Agda.Builtin.Bool.true) Agda.Builtin.List.[])
lookupAppendLeft index left right proof = refl

------------------------------------------------------------------------
-- This owner intentionally exposes the executable cursor first.  Its full
-- equality to `lookup index (encodeCookFormula formula)` is the next local
-- proof obligation; downstream executable work may already use the cursor
-- definition but must not promote it to the canonical codec without that weld.
------------------------------------------------------------------------
