-- Integration proof candidate: transitive original gamma/graph owner safety
-- not yet kernel certified. Do not assert Agda --safe until its
-- dependency closure is checked under pinned Agda 2.9.
module DASHI.Mathematics.Complexity.Karp21NativeBinaryCountBudgetExact where

------------------------------------------------------------------------
-- B4 original N21 graph-word COUNT GUARD, actually binary executable.
--
-- Source wire: gamma(n), gamma(m), then m triples of gamma fields.
-- Original FinFree guards 3*m <= length remaining before m-loop.
-- Gamma(m) can denote an exponentially large Nat, so the executable
-- guard must not construct m as unary Nat or allocate m edges first.
--
-- lengthLE computes remaining input length as LE bits by one
-- structurally decreasing scan over the ACTUAL input list; 3*m uses
-- the real ripple addBits twice; atLeast is the original bit-native
-- comparator. Numerics are used ONLY in the proof observations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.List.Base using (length)
open import Relation.Binary.PropositionalEquality using (trans; cong; sym)
open import Data.Nat.Tactic.RingSolver using (solve)
import Data.Nat.Properties as NatP
import Data.Nat.Base as Nat

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderExact as Add
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdExact as Compare
import DASHI.Mathematics.Complexity.Karp21NativeThresholdOriginalSignedDecisionExact as Decision

-- This implementation scans the actual bit-list, not Nat(length).
-- It therefore does not allocate a unary length proportional to a
-- decoded graph vertex count. Its output bit-width is logarithmic
-- in the ACTUAL list length.
lengthLE : Word.BitWord → Word.BitWord
lengthLE [] = []
lengthLE (_ ∷ rest) =
  Add.addBits (true ∷ []) (lengthLE rest)

threeTimesLE : Word.BitWord → Word.BitWord
threeTimesLE mLE =
  Add.addBits mLE (Add.addBits mLE mLE)

-- TRUE only if the entire original 3*m signed-edge-field budget fits
-- within the ACTUAL remaining suffix's length.
-- The return value is bit-native; no original Nat m multiplication.
binaryCountBudget : Word.BitWord → Word.BitWord → Bool
binaryCountBudget mLE remaining =
  Compare.atLeast (lengthLE remaining) (threeTimesLE mLE)

lengthLEValue :
  (bits : Word.BitWord) →
  Value.valueLE (lengthLE bits) ≡ length bits
lengthLEValue [] = refl
lengthLEValue (_ ∷ rest) =
  trans
    (Value.addBitsValue (true ∷ []) (lengthLE rest))
    (cong suc (lengthLEValue rest))

threeTimesLEValue :
  (mLE : Word.BitWord) →
  Value.valueLE (threeTimesLE mLE) ≡
    (suc (suc (suc zero))) * Value.valueLE mLE
threeTimesLEValue mLE =
  trans
    (Value.addBitsValue mLE (Add.addBits mLE mLE))
    (trans
      (cong (λ n → Value.valueLE mLE + n)
        (Value.addBitsValue mLE mLE))
      (solve (Value.valueLE mLE ∷ [])))

-- EXACT same numerical source guard 3*m <= length(rest).
-- This is the mathematical proof of the *executable binary guard*;
-- no bit tape/time claim follows merely from numeric correctness.
binaryCountBudgetSameOriginal :
  (mLE remaining : Word.BitWord) →
  binaryCountBudget mLE remaining
    ≡ Nat._≤ᵇ_
        ((suc (suc (suc zero))) * Value.valueLE mLE)
        (length remaining)
binaryCountBudgetSameOriginal mLE remaining =
  trans
    (Decision.compareAtLeastNumericalBoolean
      (lengthLE remaining) (threeTimesLE mLE))
    (trans
      (cong
        (λ n → Nat._≤ᵇ_ n (Value.valueLE (lengthLE remaining)))
        (threeTimesLEValue mLE))
      (cong
        (Nat._≤ᵇ_ ((suc (suc (suc zero))) * Value.valueLE mLE))
        (lengthLEValue remaining)))
