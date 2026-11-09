{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21NativeBinaryAdderWidthBoundExact where

------------------------------------------------------------------------
-- F2 physical cost prerequisite: actual output BIT-WIDTH of the
-- original executable native ripple-carry adder, including unequal
-- operand lengths and the final carry. No arithmetic value is
-- reconstructed; the proof recurses on the real original addCarry.
--
-- This is NOT a full Turing head/tape allocation or NP clock proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.List.Base using (length)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderExact as Add

-- A complete ripple stage may produce one extra most-significant
-- carry bit, but no other unbounded allocation.
addCarryOutputBitWidthLinear :
  (xs ys : Word.BitWord) (carry : Bool) →
  length (Add.addCarry xs ys carry)
    ≤ suc (length xs + length ys)
addCarryOutputBitWidthLinear [] [] false = z≤n
addCarryOutputBitWidthLinear [] [] true = s≤s z≤n
addCarryOutputBitWidthLinear (a ∷ as) [] carry
  with Add.fullAdder a false carry
... | sum , next =
  s≤s (addCarryOutputBitWidthLinear as [] next)
addCarryOutputBitWidthLinear [] (b ∷ bs) carry
  with Add.fullAdder false b carry
... | sum , next =
  s≤s (addCarryOutputBitWidthLinear [] bs next)
addCarryOutputBitWidthLinear (a ∷ as) (b ∷ bs) carry
  rewrite NatP.+-suc (length as) (length bs)
  with Add.fullAdder a b carry
... | sum , next =
  s≤s
    (NatP.≤-step
      (addCarryOutputBitWidthLinear as bs next))

addBitsOutputBitWidthLinear :
  (xs ys : Word.BitWord) →
  length (Add.addBits xs ys)
    ≤ suc (length xs + length ys)
addBitsOutputBitWidthLinear xs ys =
  addCarryOutputBitWidthLinear xs ys false

-- The actual binary graph header budget computes m + (m + m).
-- This is an explicit finite width bound on THAT source expression;
-- no original unary m is needed to execute it.
threeTimesNativeWidthBound :
  (mLE : Word.BitWord) →
  length (Add.addBits mLE (Add.addBits mLE mLE))
    ≤ suc (length mLE + length (Add.addBits mLE mLE))
threeTimesNativeWidthBound mLE =
  addBitsOutputBitWidthLinear mLE (Add.addBits mLE mLE)
