{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact where

------------------------------------------------------------------------
-- K05: WHOLE-WORD NUMERIC CORRECTNESS OF THE EXECUTABLE BIT ADDER.
--
-- Numerical interpretation is proof-side only; the original addCarry
-- implementation executes Boolean full-adder cases and list recursion.
-- The integer score accumulator still needs signed subtraction, a
-- correctly specified binary comparison and all-word graph integration.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Nat.Tactic.RingSolver using (solve)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderExact as Add

two : Nat
two = suc (suc zero)

-- The represented number is only a mathematical observation.
valueLE : Word.BitWord → Nat
valueLE [] = zero
valueLE (bit ∷ rest) = Add.bitValue bit + two * valueLE rest

leftPolynomialIdentity :
  (s k x y : Nat) →
  s + two * (x + y + k) ≡
  (s + two * k) + two * (x + y)
leftPolynomialIdentity s k x y = solve (s ∷ k ∷ x ∷ y ∷ [])

rightPolynomialIdentity :
  (a b c x y : Nat) →
  (a + two * x) + (b + two * y) + c ≡
  (a + b + c) + two * (x + y)
rightPolynomialIdentity a b c x y = solve (a ∷ b ∷ c ∷ x ∷ y ∷ [])

carryAlgebra :
  (a b c s k x y : Nat) →
  a + b + c ≡ s + two * k →
  s + two * (x + y + k) ≡
    (a + two * x) + (b + two * y) + c
carryAlgebra a b c s k x y local =
  trans
    (leftPolynomialIdentity s k x y)
    (trans
      (cong (λ n → n + two * (x + y)) (sym local))
      (sym (rightPolynomialIdentity a b c x y)))

-- Carries are accounted for as incoming bits, including unequal
-- encoded lengths and a final carry beyond both input words.
addCarryValue :
  (xs ys : Word.BitWord) (incoming : Bool) →
  valueLE (Add.addCarry xs ys incoming) ≡
    valueLE xs + valueLE ys + Add.bitValue incoming
addCarryValue [] [] false = refl
addCarryValue [] [] true = refl
addCarryValue (a ∷ as) [] incoming
  with Add.fullAdder a false incoming |
       Add.fullAdderLocalCorrect a false incoming
... | (sum , next) | local =
  trans
    (cong (λ n → Add.bitValue sum + two * n)
      (addCarryValue as [] next))
    (carryAlgebra
      (Add.bitValue a) zero (Add.bitValue incoming)
      (Add.bitValue sum) (Add.bitValue next)
      (valueLE as) zero local)
addCarryValue [] (b ∷ bs) incoming
  with Add.fullAdder false b incoming |
       Add.fullAdderLocalCorrect false b incoming
... | (sum , next) | local =
  trans
    (cong (λ n → Add.bitValue sum + two * n)
      (addCarryValue [] bs next))
    (carryAlgebra
      zero (Add.bitValue b) (Add.bitValue incoming)
      (Add.bitValue sum) (Add.bitValue next)
      zero (valueLE bs) local)
addCarryValue (a ∷ as) (b ∷ bs) incoming
  with Add.fullAdder a b incoming |
       Add.fullAdderLocalCorrect a b incoming
... | (sum , next) | local =
  trans
    (cong (λ n → Add.bitValue sum + two * n)
      (addCarryValue as bs next))
    (carryAlgebra
      (Add.bitValue a) (Add.bitValue b) (Add.bitValue incoming)
      (Add.bitValue sum) (Add.bitValue next)
      (valueLE as) (valueLE bs) local)

addBitsValue :
  (xs ys : Word.BitWord) →
  valueLE (Add.addBits xs ys) ≡ valueLE xs + valueLE ys
addBitsValue xs ys = addCarryValue xs ys false
