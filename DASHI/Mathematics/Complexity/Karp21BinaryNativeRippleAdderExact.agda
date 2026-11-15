{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderExact where

------------------------------------------------------------------------
-- K05: CONCRETE BINARY-NATIVE RIPPLE-CARRY ADDITION.
--
-- The input and output are little-endian bit lists. No unary Nat
-- arithmetic is executed by addCarry; Nat is used only in proof-side
-- local specifications and cost accounting.
--
-- This is a reusable source for signed score accumulation. A complete
-- signed representation, subtraction, graph-loop integration and a
-- tape-machine clock remain separate obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.List.Base using (length)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_)
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word

bitValue : Bool → Nat
bitValue false = zero
bitValue true = suc zero

-- Sum and carry of three actual input bits. The case table is entirely
-- executable and independent of the magnitudes represented by the words.
fullAdder : Bool → Bool → Bool → Bool × Bool
fullAdder false false false = false , false
fullAdder false false true  = true  , false
fullAdder false true  false = true  , false
fullAdder false true  true  = false , true
fullAdder true  false false = true  , false
fullAdder true  false true  = false , true
fullAdder true  true  false = false , true
fullAdder true  true  true  = true  , true

-- Every row satisfies a+b+carry = sum+2*newCarry.
fullAdderLocalCorrect :
  (a b carry : Bool) →
  bitValue a + bitValue b + bitValue carry ≡
  bitValue (Data.Product.proj₁ (fullAdder a b carry))
    + (suc (suc zero)) *
      bitValue (Data.Product.proj₂ (fullAdder a b carry))
fullAdderLocalCorrect false false false = refl
fullAdderLocalCorrect false false true = refl
fullAdderLocalCorrect false true false = refl
fullAdderLocalCorrect false true true = refl
fullAdderLocalCorrect true false false = refl
fullAdderLocalCorrect true false true = refl
fullAdderLocalCorrect true true false = refl
fullAdderLocalCorrect true true true = refl

-- LSB-first ripple carry with implicit zero extension. Every step
-- consumes at least one real source bit. It therefore terminates
-- structurally and does not expand numbers to unary Nat values.
addCarry : Word.BitWord → Word.BitWord → Bool → Word.BitWord
addCarry [] [] false = []
addCarry [] [] true = true ∷ []
addCarry (a ∷ as) [] carry
  with fullAdder a false carry
... | sum , next = sum ∷ addCarry as [] next
addCarry [] (b ∷ bs) carry
  with fullAdder false b carry
... | sum , next = sum ∷ addCarry [] bs next
addCarry (a ∷ as) (b ∷ bs) carry
  with fullAdder a b carry
... | sum , next = sum ∷ addCarry as bs next

addBits : Word.BitWord → Word.BitWord → Word.BitWord
addBits xs ys = addCarry xs ys false

-- Structural work is counted without running any proof-side numeric
-- conversion. One unit is charged per ripple stage and terminal test.
additionInspectionWork :
  Word.BitWord → Word.BitWord → Nat
additionInspectionWork [] [] = suc zero
additionInspectionWork (_ ∷ as) [] =
  suc (additionInspectionWork as [])
additionInspectionWork [] (_ ∷ bs) =
  suc (additionInspectionWork [] bs)
additionInspectionWork (_ ∷ as) (_ ∷ bs) =
  suc (additionInspectionWork as bs)

-- Each ripple stage consumes at least one source bit; the exact
-- schedule is bounded by the total encoded input width plus one.
additionInspectionLinear :
  (xs ys : Word.BitWord) →
  additionInspectionWork xs ys ≤ suc (length xs + length ys)
additionInspectionLinear [] [] = s≤s z≤n
additionInspectionLinear (a ∷ as) [] =
  s≤s (additionInspectionLinear as [])
additionInspectionLinear [] (b ∷ bs) =
  s≤s (additionInspectionLinear [] bs)
additionInspectionLinear (a ∷ as) (b ∷ bs)
  rewrite NatP.+-suc (length as) (length bs) =
  s≤s (NatP.≤-step (additionInspectionLinear as bs))
