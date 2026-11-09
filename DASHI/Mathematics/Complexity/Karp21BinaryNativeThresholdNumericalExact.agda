{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdNumericalExact where

------------------------------------------------------------------------
-- P0-E: ALL-WORD MATHEMATICAL CORRECTNESS OF THE ORIGINAL compareLE.
-- Witness-form trichotomy avoids an untrusted numerical comparator:
--   less    -> right = suc(left + gap)
--   equal   -> left = right
--   greater -> left = suc(right + gap)
--
-- This proof consumes the ACTUAL recursive bitwise compareLE and the
-- already-proved little-endian source valueLE. It works for any
-- widths, including redundant most-significant zeros. It never
-- changes the executable comparator to a Nat-producing algorithm.
--
-- Source owner: Karp21BinaryNativeThresholdExact.compareLE and
-- Karp21BinaryNativeRippleAdderValueExact.valueLE.
-- Agda kernel acceptance is a separate referee gate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Nat.Tactic.RingSolver using (solve)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdExact as Compare
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderExact as Add
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value

two : Nat
two = suc (suc zero)

-- Constructive strictness witnesses can be converted to ordinary
-- Nat < after the main proof, with no excluded-middle shortcut.
OrderingWitness : Compare.BitOrdering → Nat → Nat → Set
OrderingWitness Compare.less x y =
  Σ Nat (λ gap → y ≡ suc (x + gap))
OrderingWitness Compare.equal x y = x ≡ y
OrderingWitness Compare.greater x y =
  Σ Nat (λ gap → x ≡ suc (y + gap))

-- A strictly higher right tail remains higher after appending ANY
-- pair of least-significant bits. The four cases pay the 0/1 bias.
liftStrictLess :
  (a b : Bool) (x y : Nat) →
  OrderingWitness Compare.less x y →
  OrderingWitness Compare.less
    (Add.bitValue a + two * x)
    (Add.bitValue b + two * y)
liftStrictLess false false x .(suc (x + gap)) (gap , refl) =
  suc (two * gap) , solve (x ∷ gap ∷ [])
liftStrictLess false true x .(suc (x + gap)) (gap , refl) =
  suc (suc (two * gap)) , solve (x ∷ gap ∷ [])
liftStrictLess true false x .(suc (x + gap)) (gap , refl) =
  two * gap , solve (x ∷ gap ∷ [])
liftStrictLess true true x .(suc (x + gap)) (gap , refl) =
  suc (two * gap) , solve (x ∷ gap ∷ [])

liftStrictGreater :
  (a b : Bool) (x y : Nat) →
  OrderingWitness Compare.greater x y →
  OrderingWitness Compare.greater
    (Add.bitValue a + two * x)
    (Add.bitValue b + two * y)
liftStrictGreater a b x y witness =
  liftStrictLess b a y x witness

-- Equal high tails: the ACTUAL orderBit controls comparison.
liftEqualTails :
  (a b : Bool) (x y : Nat) →
  x ≡ y →
  OrderingWitness (Compare.orderBit a b)
    (Add.bitValue a + two * x)
    (Add.bitValue b + two * y)
liftEqualTails false false x .x refl = refl
liftEqualTails false true x .x refl =
  zero , solve (x ∷ [])
liftEqualTails true false x .x refl =
  zero , solve (x ∷ [])
liftEqualTails true true x .x refl = refl

-- This is the exact local extension rule used by compareLE:
-- higher bits override lower bits only when their order is decided.
liftCompareWitness :
  (a b : Bool) (x y : Nat) (higher : Compare.BitOrdering) →
  OrderingWitness higher x y →
  OrderingWitness
    (Compare.selectHigh higher (Compare.orderBit a b))
    (Add.bitValue a + two * x)
    (Add.bitValue b + two * y)
liftCompareWitness a b x y Compare.less witness =
  liftStrictLess a b x y witness
liftCompareWitness a b x y Compare.equal witness =
  liftEqualTails a b x y witness
liftCompareWitness a b x y Compare.greater witness =
  liftStrictGreater a b x y witness

-- FULL ORIGINAL recursive comparator: all widths and all bitwords.
-- The [] versus nonempty cases use the comparator's ACTUAL implicit
-- zero extension, not a list-length ordering shortcut.
compareLENumericalCorrect :
  (xs ys : Word.BitWord) →
  OrderingWitness (Compare.compareLE xs ys)
    (Value.valueLE xs) (Value.valueLE ys)
compareLENumericalCorrect [] [] = refl
compareLENumericalCorrect (a ∷ xs) [] =
  liftCompareWitness a false (Value.valueLE xs) zero
    (Compare.compareLE xs [])
    (compareLENumericalCorrect xs [])
compareLENumericalCorrect [] (b ∷ ys) =
  liftCompareWitness false b zero (Value.valueLE ys)
    (Compare.compareLE [] ys)
    (compareLENumericalCorrect [] ys)
compareLENumericalCorrect (a ∷ xs) (b ∷ ys) =
  liftCompareWitness a b (Value.valueLE xs) (Value.valueLE ys)
    (Compare.compareLE xs ys)
    (compareLENumericalCorrect xs ys)

-- Exact accepted/rejected classification of the native atLeast,
-- without relying on a Boolean Nat comparison oracle.
data AtLeastNumericalWitness (x y : Nat) : Set where
  equalValues : x ≡ y → AtLeastNumericalWitness x y
  greaterValues :
    (gap : Nat) → x ≡ suc (y + gap) →
    AtLeastNumericalWitness x y

atLeastTrueGivesNumericalOrder :
  (xs ys : Word.BitWord) →
  Compare.atLeast xs ys ≡ true →
  AtLeastNumericalWitness (Value.valueLE xs) (Value.valueLE ys)
atLeastTrueGivesNumericalOrder xs ys passed
  with Compare.compareLE xs ys
     | compareLENumericalCorrect xs ys
... | Compare.less | (gap , equation) with passed
... | ()
... | Compare.equal | equation = equalValues equation
... | Compare.greater | (gap , equation) =
  greaterValues gap equation

atLeastFalseGivesNumericalOrder :
  (xs ys : Word.BitWord) →
  Compare.atLeast xs ys ≡ false →
  Σ Nat (λ gap →
    Value.valueLE ys ≡ suc (Value.valueLE xs + gap))
atLeastFalseGivesNumericalOrder xs ys rejected
  with Compare.compareLE xs ys
     | compareLENumericalCorrect xs ys
... | Compare.less | witness = witness
... | Compare.equal | equation with rejected
... | ()
... | Compare.greater | witness with rejected
... | ()
