module DASHI.Mathematics.Complexity.Karp21NativeBinaryStrictAfterOriginalExact where

------------------------------------------------------------------------
-- B1: ACTUAL original Graph.strictAfter, all binary padded encodings.
-- No substitute semantic meaning: compare the real source
-- strictAfterBinary against the original NatP._<?_ / _≟_ branches.
--
-- The executable strictAfterBinary never computes Nat magnitudes.
-- Numerical observations and NatP decision reflection are proof-only.
-- Kernel acceptance requires the pinned original transitive imports.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NatP
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Original
import DASHI.Mathematics.Complexity.Karp21NativeBinaryEndpointValidatorExact as Binary
import DASHI.Mathematics.Complexity.Karp21BinaryNativeThresholdExact as Compare
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21NativeNatDecisionReflectionExact as Decision

observePrevious : Binary.BinaryPreviousPair → Original.PreviousPair
observePrevious Binary.noPrevious = Original.noPrevious
observePrevious (Binary.previous a b) =
  Original.previous (Value.valueLE a) (Value.valueLE b)

-- Mirror Nat Boolean branching, never executed in native validator.
strictAfterNumericBoolean :
  Original.PreviousPair → Nat → Nat → Bool
strictAfterNumericBoolean Original.noPrevious u v = true
strictAfterNumericBoolean (Original.previous a b) u v
  with Nat._≤ᵇ_ (suc a) u
... | true = true
... | false with Nat._≡ᵇ_ a u
... | false = false
... | true = Nat._≤ᵇ_ (suc b) v

-- First identify this proof-side evaluator with the LITERAL
-- Graph.strictAfter owner, including strictly ascending endpoints.
strictAfterNumericSameOriginal :
  (previous : Original.PreviousPair) (u v : Nat) →
  strictAfterNumericBoolean previous u v
    ≡ Original.strictAfter previous u v
strictAfterNumericSameOriginal Original.noPrevious u v = refl
strictAfterNumericSameOriginal (Original.previous a b) u v
  rewrite Decision.natStrictDecisionSameBoolean a u
        | Decision.natEqualDecisionSameBoolean a u
        | Decision.natStrictDecisionSameBoolean b v
  with NatP._<?_ a u
... | yes _ = refl
... | no _ with NatP._≟_ a u
... | no _ = refl
... | yes _ with NatP._<?_ b v
... | yes _ = refl
... | no _ = refl

-- Core binary LEX compare against proof-side numeric branching.
-- The real comparator supplies the less/equal/greater alternatives;
-- numeric correctness was paid in Karp21NativeBinaryEndpointValidator.
strictAfterBinarySameNumeric :
  (previous : Binary.BinaryPreviousPair)
  (u v : Word.BitWord) →
  Binary.strictAfterBinary previous u v
    ≡ strictAfterNumericBoolean
        (observePrevious previous) (Value.valueLE u) (Value.valueLE v)
strictAfterBinarySameNumeric Binary.noPrevious u v = refl
strictAfterBinarySameNumeric (Binary.previous a b) u v
  with Compare.compareLE a u
... | Compare.less
  rewrite sym (Binary.nativeStrictLessNumerical a u) = refl
... | Compare.equal
  rewrite sym (Binary.nativeStrictLessNumerical a u)
        | sym (Binary.nativeEqualNumerical a u)
        | sym (Binary.nativeStrictLessNumerical b v) = refl
... | Compare.greater
  rewrite sym (Binary.nativeStrictLessNumerical a u)
        | sym (Binary.nativeEqualNumerical a u) = refl

-- B1 EXACT original source lexicographic condition on u/v, including
-- noncanonical padded LE binary words and reversed/duplicate edges.
nativeBinaryStrictAfterSameOriginal :
  (previous : Binary.BinaryPreviousPair)
  (u v : Word.BitWord) →
  Binary.strictAfterBinary previous u v
    ≡ Original.strictAfter
        (observePrevious previous) (Value.valueLE u) (Value.valueLE v)
nativeBinaryStrictAfterSameOriginal previous u v =
  trans
    (strictAfterBinarySameNumeric previous u v)
    (strictAfterNumericSameOriginal
      (observePrevious previous) (Value.valueLE u) (Value.valueLE v))
