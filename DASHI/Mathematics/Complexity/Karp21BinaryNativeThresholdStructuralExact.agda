{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdStructuralExact where

------------------------------------------------------------------------
-- Source original binary comparator: structural/cost theorems.
-- This works on the genuine Karp21BinaryNativeThresholdExact.compareLE,
-- NOT a replacement comparator. All binary widths/zero-padding valid.
-- A full atLeast <-> Nat <= theorem remains an independent P0-E gate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.List.Base using (length)
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdExact as Compare

-- Lower bits can never override an already-decided higher position.
selectHighEqual : (ord : Compare.BitOrdering) →
  Compare.selectHigh Compare.equal ord ≡ ord
selectHighEqual ord = refl

selectHighLess : (ord : Compare.BitOrdering) →
  Compare.selectHigh Compare.less ord ≡ Compare.less
selectHighLess ord = refl

selectHighGreater : (ord : Compare.BitOrdering) →
  Compare.selectHigh Compare.greater ord ≡ Compare.greater
selectHighGreater ord = refl

sameBitIsEqual : (b : Bool) →
  Compare.orderBit b b ≡ Compare.equal
sameBitIsEqual false = refl
sameBitIsEqual true = refl

-- Comparison of a genuine source bitword with itself is equal,
-- including any leading high zeros.
compareLEReflexive : (xs : Word.BitWord) →
  Compare.compareLE xs xs ≡ Compare.equal
compareLEReflexive [] = refl
compareLEReflexive (b ∷ rest)
  rewrite compareLEReflexive rest | sameBitIsEqual b = refl

atLeastReflexive : (xs : Word.BitWord) →
  Compare.atLeast xs xs ≡ true
atLeastReflexive xs rewrite compareLEReflexive xs = refl

-- A shared least significant bit never changes the original
-- comparator outcome, since the remaining higher bits dominate.
compareLESameLowBit :
  (b : Bool) (xs ys : Word.BitWord) →
  Compare.compareLE (b ∷ xs) (b ∷ ys)
    ≡ Compare.compareLE xs ys
compareLESameLowBit b xs ys
  with Compare.compareLE xs ys
... | Compare.less = refl
... | Compare.equal rewrite sameBitIsEqual b = refl
... | Compare.greater = refl

atLeastSameLowBit :
  (b : Bool) (xs ys : Word.BitWord) →
  Compare.atLeast (b ∷ xs) (b ∷ ys)
    ≡ Compare.atLeast xs ys
atLeastSameLowBit b xs ys
  rewrite compareLESameLowBit b xs ys
  with Compare.compareLE xs ys
... | Compare.less = refl
... | Compare.equal = refl
... | Compare.greater = refl

-- This counts EXACT structural compareLE recursive frames, including
-- zero-extension and the terminating []/[] observation. It does NOT
-- assume O(1) random access to the input bit lists.
compareInspectionWork :
  Word.BitWord → Word.BitWord → Nat
compareInspectionWork [] [] = suc zero
compareInspectionWork (_ ∷ xs) [] =
  suc (compareInspectionWork xs [])
compareInspectionWork [] (_ ∷ ys) =
  suc (compareInspectionWork [] ys)
compareInspectionWork (_ ∷ xs) (_ ∷ ys) =
  suc (compareInspectionWork xs ys)

-- Total actual bit-reader recursive frames <= length xs + length ys + 1.
compareInspectionLinear :
  (xs ys : Word.BitWord) →
  compareInspectionWork xs ys ≤ suc (length xs + length ys)
compareInspectionLinear [] [] = s≤s z≤n
compareInspectionLinear (b ∷ xs) [] =
  s≤s (compareInspectionLinear xs [])
compareInspectionLinear [] (b ∷ ys) =
  s≤s (compareInspectionLinear [] ys)
compareInspectionLinear (a ∷ xs) (b ∷ ys)
  rewrite NatP.+-suc (length xs) (length ys) =
  s≤s (NatP.≤-step (compareInspectionLinear xs ys))
