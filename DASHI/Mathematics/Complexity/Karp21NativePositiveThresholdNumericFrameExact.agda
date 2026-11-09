{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21NativePositiveThresholdNumericFrameExact where

------------------------------------------------------------------------
-- P0-E source N21 positive-threshold arithmetic on original gamma
-- FRAMES. The genuine native readPositiveGammaLE runs a binary
-- predecessor on the gamma-successor numeral. Its mathematical value
-- is precisely the original gamma(n) Nat, not the successor n+1.
--
-- All-word accepted/rejected lifting to the complete original graph
-- header is still separately open; this theorem is about every
-- complete source gamma frame and its unchanged suffix.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (reverse; _++_; length)
import Data.List.Properties as ListP
import Data.Nat.Properties as NatP
open import Data.Nat.Base using (_∸_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Old
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21GammaBinarySignedPayloadValueCutExact as Frame
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Gamma
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21SignedGammaBinaryValueArithmeticExact as Binary
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive

anyOneAppendOne :
  (bits : Word.BitWord) →
  Positive.anyOne (bits ++ (true ∷ [])) ≡ true
anyOneAppendOne [] = refl
anyOneAppendOne (false ∷ bits) = anyOneAppendOne bits
anyOneAppendOne (true ∷ bits) = refl

-- Every canonical Elias-gamma successor numeral has a high one, so
-- the actual predecessorLEValue theorem is applicable without a
-- caller-provided nonzero premise.
anyOneReverseGammaSuccessor :
  (payload : Word.BitWord) →
  Positive.anyOne (reverse (true ∷ payload)) ≡ true
anyOneReverseGammaSuccessor payload
  rewrite ListP.reverse-++ (true ∷ []) payload =
  anyOneAppendOne (reverse payload)

-- The actual native binary predecessor yields original gamma(n)
-- rather than its successor. This is a numerical theorem on the
-- genuine executable predecessor of arbitrary source payloads.
nativePredecessorValueSameOriginalGamma :
  (payload : Word.BitWord) →
  Value.valueLE
    (Positive.predecessorLE (reverse (true ∷ payload)))
    ≡
    (Old.pow2 (length payload) + Old.payloadValue payload)
      ∸ suc zero
nativePredecessorValueSameOriginalGamma payload
  with Binary.sourceMagnitudePositive payload
... | k , positive
  rewrite positive =
  NatP.suc-injective
    (trans
      (sym (NatP.+-comm
        (Value.valueLE
          (Positive.predecessorLE (reverse (true ∷ payload))))
        (suc zero)))
      (trans
        (Positive.predecessorLEValue
          (reverse (true ∷ payload))
          (anyOneReverseGammaSuccessor payload))
        (trans
          (Binary.nativeMagnitudeSameOriginalBinaryValue payload)
          positive)))

-- The same original wire suffix is not consumed by predecessor; the
-- arithmetic proof above therefore identifies the exact original
-- source threshold magnitude that the positive-only native parser
-- is supposed to return.
