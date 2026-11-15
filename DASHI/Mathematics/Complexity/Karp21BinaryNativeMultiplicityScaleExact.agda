{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21BinaryNativeMultiplicityScaleExact where

------------------------------------------------------------------------
-- K05 original N21 signed trace reuse: ONE binary operation per weight
-- class and binary multiplicity, rather than k repeated huge additions.
--
-- The source FRACTRAN/SSP machine motivates the valuation/count factor,
-- but this exact executor acts on ORIGINAL Karp binary magnitudes, not
-- a Monster action, prime-power integer, or Peano Nat exponent.
--
-- Both inputs are LSB-first. Structural recursion is on multiplicity
-- BITS and terminates regardless of the VALUE it represents.
--
-- Karp (1972); DASHI original signed-gamma/ripple-adder owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Nat.Tactic.RingSolver using (solve)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderExact as Add
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value

-- Multiply a binary magnitude by a binary count.
-- The count 2k+1 adds the magnitude once; count 2k only shifts the
-- recursively accumulated value. Neither case reconstructs unary k.
scaleBits :
  Word.BitWord → Word.BitWord → Word.BitWord
scaleBits weight [] = []
scaleBits weight (false ∷ count) =
  false ∷ scaleBits weight count
scaleBits weight (true ∷ count) =
  Add.addBits weight (false ∷ scaleBits weight count)

two : Nat
two = suc (suc zero)

falseScaleAlgebra :
  (w k : Nat) →
  two * (w * k) ≡ w * (two * k)
falseScaleAlgebra w k = solve (w ∷ k ∷ [])

trueScaleAlgebra :
  (w k : Nat) →
  w + two * (w * k) ≡ w * (suc (two * k))
trueScaleAlgebra w k = solve (w ∷ k ∷ [])

-- Mathematical observation only: the executable source uses addBits,
-- a finite bit shift, and recursion over the original multiplicity bits.
scaleBitsValue :
  (weight count : Word.BitWord) →
  Value.valueLE (scaleBits weight count) ≡
    Value.valueLE weight * Value.valueLE count
scaleBitsValue weight [] =
  sym (NatP.*-zeroʳ (Value.valueLE weight))
scaleBitsValue weight (false ∷ count) =
  trans
    (cong (λ n → two * n) (scaleBitsValue weight count))
    (falseScaleAlgebra
      (Value.valueLE weight) (Value.valueLE count))
scaleBitsValue weight (true ∷ count) =
  trans
    (Value.addBitsValue weight
      (false ∷ scaleBits weight count))
    (trans
      (cong
        (λ n → Value.valueLE weight + two * n)
        (scaleBitsValue weight count))
      (trueScaleAlgebra
        (Value.valueLE weight) (Value.valueLE count)))

-- One full shift/add pass per multiplicity bit; NOT per natural
-- magnitude. A full bit-tape clock must additionally price copying,
-- allocation, sharing and access to the weight-class dictionary.
scaleBitRounds : Word.BitWord → Nat
scaleBitRounds [] = zero
scaleBitRounds (_ ∷ rest) = suc (scaleBitRounds rest)
