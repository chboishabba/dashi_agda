{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21CookUnaryIndexWordBoundExact where

------------------------------------------------------------------------
-- K00 SAT: ORIGINAL COOK UNARY VARIABLE INDICES ARE INPUT-BOUNDED.
--
-- Prefix.encodeNatInto encodes a Nat i by i natSuccToken entries,
-- then natZeroToken. The fixed 3-bit code therefore pays for each
-- successor in the actual STRICT SAT input Word, unlike the E20/N21
-- gamma-coded vertex count, which may be exponentially large.
--
-- Every syntactic occurrence's Nat index is at most the source-owned
-- Cook token count and, for every successfully strict-parsed word,
-- at most Word.encodingSize of that SAME original input word.
--
-- This is a representation/size proof. It does NOT assert an ordinary
-- Turing machine runtime, index-comparison clock, or PR.InNP.
--
-- Cook (1971), Leonid Levin (1973); original DASHI prefix, strict
-- Cook parser, compact occurrence checker and bitword codec owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Maybe.Base using (just)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaPrefixCodecExact as Prefix
import DASHI.Mathematics.Complexity.PNotEqualsNPCookFormulaBinaryCodecExact as Binary
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21CookFiniteOccurrenceWitnessExact as Finite
import DASHI.Mathematics.Complexity.Karp21CookStrictTripleBitBoundaryExact as Strict
import DASHI.Mathematics.Complexity.Karp21CookStrictWordCanonicalReencodeExact as Canonical

-- All indices in the original occurrence list share one size bound.
AllIndicesWithin : Nat → List Nat → Set
AllIndicesWithin cap [] = ⊤
AllIndicesWithin cap (i ∷ rest) =
  (i ≤ cap) × AllIndicesWithin cap rest

withinLift :
  ∀ {old new}
    (indices : List Nat) →
  AllIndicesWithin old indices →
  old ≤ new →
  AllIndicesWithin new indices
withinLift [] all limit = tt
withinLift (i ∷ rest) (head , tail) limit =
  NatP.≤-trans head limit , withinLift rest tail limit

withinAppend :
  ∀ {cap}
    (xs ys : List Nat) →
  AllIndicesWithin cap xs →
  AllIndicesWithin cap ys →
  AllIndicesWithin cap (xs ++ ys)
withinAppend [] ys left right = right
withinAppend (i ∷ rest) ys (head , tail) right =
  head , withinAppend rest ys tail right

naturalAtMostSuccessor : (n : Nat) → n ≤ suc n
naturalAtMostSuccessor zero = z≤n
naturalAtMostSuccessor (suc n) =
  s≤s (naturalAtMostSuccessor n)

leftAtMostSum : (left right : Nat) → left ≤ left + right
leftAtMostSum zero right = z≤n
leftAtMostSum (suc left) right =
  s≤s (leftAtMostSum left right)

rightAtMostSum : (left right : Nat) → right ≤ left + right
rightAtMostSum zero right = NatP.≤-refl
rightAtMostSum (suc left) right =
  NatP.≤-trans (rightAtMostSum left right)
    (naturalAtMostSuccessor (left + right))

leftAtMostOnePlusSum :
  (left right : Nat) → left ≤ suc (left + right)
leftAtMostOnePlusSum left right =
  NatP.≤-trans (leftAtMostSum left right)
    (naturalAtMostSuccessor (left + right))

rightAtMostOnePlusSum :
  (left right : Nat) → right ≤ suc (left + right)
rightAtMostOnePlusSum left right =
  NatP.≤-trans (rightAtMostSum left right)
    (naturalAtMostSuccessor (left + right))

indexWithinUnaryTokenCount :
  (i : Nat) → i ≤ Prefix.natTokenCount i
indexWithinUnaryTokenCount zero = z≤n
indexWithinUnaryTokenCount (suc i) =
  s≤s (indexWithinUnaryTokenCount i)

-- Induction over the source-owned Cook formula, not an alternative AST.
formulaIndexTokenBound :
  (formula : Cook.BooleanFormula) →
  AllIndicesWithin
    (Prefix.cookFormulaTokenCount formula)
    (Finite.formulaVariables formula)
formulaIndexTokenBound (Cook.variable i) =
  (NatP.≤-trans
     (indexWithinUnaryTokenCount i)
     (naturalAtMostSuccessor (Prefix.natTokenCount i)))
  , tt
formulaIndexTokenBound (Cook.constant value) = tt
formulaIndexTokenBound (Cook.negate formula) =
  withinLift
    (Finite.formulaVariables formula)
    (formulaIndexTokenBound formula)
    (naturalAtMostSuccessor (Prefix.cookFormulaTokenCount formula))
formulaIndexTokenBound (Cook.conjunction left right) =
  withinAppend
    (Finite.formulaVariables left) (Finite.formulaVariables right)
    (withinLift
      (Finite.formulaVariables left)
      (formulaIndexTokenBound left)
      (leftAtMostOnePlusSum
        (Prefix.cookFormulaTokenCount left)
        (Prefix.cookFormulaTokenCount right)))
    (withinLift
      (Finite.formulaVariables right)
      (formulaIndexTokenBound right)
      (rightAtMostOnePlusSum
        (Prefix.cookFormulaTokenCount left)
        (Prefix.cookFormulaTokenCount right)))
formulaIndexTokenBound (Cook.disjunction left right) =
  withinAppend
    (Finite.formulaVariables left) (Finite.formulaVariables right)
    (withinLift
      (Finite.formulaVariables left)
      (formulaIndexTokenBound left)
      (leftAtMostOnePlusSum
        (Prefix.cookFormulaTokenCount left)
        (Prefix.cookFormulaTokenCount right)))
    (withinLift
      (Finite.formulaVariables right)
      (formulaIndexTokenBound right)
      (rightAtMostOnePlusSum
        (Prefix.cookFormulaTokenCount left)
        (Prefix.cookFormulaTokenCount right)))

-- Use source-owned exact 3-token encoding and the strict parser's
-- already-proved left inverse to transfer the bound to ANY accepted
-- input word, not just the canonical encoder output by itself.
strictWordTokenCountBound :
  (word : Word.BitWord) (formula : Cook.BooleanFormula) →
  Strict.strictDecodeCookFormulaBits word ≡ just formula →
  Prefix.cookFormulaTokenCount formula ≤ Word.encodingSize word
strictWordTokenCountBound word formula decoded =
  subst
    (λ actualWord →
      Prefix.cookFormulaTokenCount formula
        ≤ Word.encodingSize actualWord)
    (Canonical.k00StrictAcceptedWordCanonicalReencode
      word formula decoded)
    (subst
      (λ size → Prefix.cookFormulaTokenCount formula ≤ size)
      (sym (Finite.canonicalCookFormulaWordSizeExact formula))
      (Finite.cookTokenCountWithinTripleCode
        (Prefix.cookFormulaTokenCount formula)))

k00StrictWordAllIndicesBounded :
  (word : Word.BitWord) (formula : Cook.BooleanFormula) →
  Strict.strictDecodeCookFormulaBits word ≡ just formula →
  AllIndicesWithin
    (Word.encodingSize word)
    (Finite.formulaVariables formula)
k00StrictWordAllIndicesBounded word formula decoded =
  withinLift
    (Finite.formulaVariables formula)
    (formulaIndexTokenBound formula)
    (strictWordTokenCountBound word formula decoded)
