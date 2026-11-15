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
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Old
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21GammaBinarySignedPayloadValueCutExact as Frame
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Gamma
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21SignedGammaAllWordFrameExtractionExact as Extract
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedSuffixExact as Suffix
import DASHI.Mathematics.Complexity.Karp21SignedGammaNativeOriginalValueExact as SignedValue
import DASHI.Mathematics.Complexity.Karp21NativePositiveThresholdNonzeroExact as Nonzero
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

------------------------------------------------------------------------
-- Strict original positive gamma threshold: SAME WORD, SAME suffix,
-- rejection at zero and malformed/truncated words. No new codec.
------------------------------------------------------------------------

observedPositiveGamma :
  Maybe (Word.BitWord × Word.BitWord) →
  Maybe (Nat × Word.BitWord)
observedPositiveGamma nothing = nothing
observedPositiveGamma (just (magnitude , suffix)) =
  just (Value.valueLE magnitude , suffix)

originalStrictPositiveGamma :
  Word.BitWord → Maybe (Nat × Word.BitWord)
originalStrictPositiveGamma word with Old.readGamma word
... | nothing = nothing
... | just (zero , suffix) = nothing
... | just (suc k , suffix) = just (suc k , suffix)

nativeGammaCanonicalFrame :
  (payload suffix : Word.BitWord) →
  Gamma.readGammaBinary (Frame.originalGammaFrame payload suffix)
    ≡ just (true ∷ payload , suffix)
nativeGammaCanonicalFrame payload suffix
  rewrite Frame.originalGoldenZeroPrefixSame (length payload)
        | Gamma.readGammaBinaryPayloadExact payload suffix = refl

-- Every complete original gamma frame: exact value and cursor, with
-- correctly rejected threshold zero and redundant zero representations.
nativePositiveGammaCanonicalFrameSameOriginal :
  (payload suffix : Word.BitWord) →
  observedPositiveGamma
    (Positive.readPositiveGammaLE
      (Frame.originalGammaFrame payload suffix))
    ≡ originalStrictPositiveGamma
      (Frame.originalGammaFrame payload suffix)
nativePositiveGammaCanonicalFrameSameOriginal payload suffix
  rewrite nativeGammaCanonicalFrame payload suffix
        | Old.readGammaPayloadExact payload suffix
        | sym (nativePredecessorValueSameOriginalGamma payload)
  with Positive.anyOne
    (Positive.predecessorLE (reverse (true ∷ payload))) in nonzero
... | false
  rewrite Nonzero.anyOneFalseMeansZero
    (Positive.predecessorLE (reverse (true ∷ payload))) nonzero = refl
... | true
  with Nonzero.anyOneTrueMeansPositive
    (Positive.predecessorLE (reverse (true ∷ payload))) nonzero
... | k , positive
  rewrite positive = refl

-- On source gamma failure the ORIGINAL readGamma also fails, not
-- merely its signed reader. This uses the earlier all-word suffix
-- theorem and forbids a native-only false positive.
originalGammaFailureFromNativeFailure :
  (word : Word.BitWord) →
  Gamma.readGammaBinary word ≡ nothing →
  Old.readGamma word ≡ nothing
originalGammaFailureFromNativeFailure word failed =
  SignedValue.suffixNoneImpliesNothing (Old.readGamma word)
    (trans
      (sym (Suffix.nativeGammaOriginalSuffixAllWords word))
      (cong Suffix.suffixBits failed))

-- All possible source input words, including malformed gamma headers,
-- incomplete payloads, zero-positive threshold and arbitrary suffix.
-- This does NOT yet validate the original complete graph-word fields.
nativePositiveThresholdParserSameOriginal :
  (word : Word.BitWord) →
  observedPositiveGamma (Positive.readPositiveGammaLE word)
    ≡ originalStrictPositiveGamma word
nativePositiveThresholdParserSameOriginal word
  with Gamma.readGammaBinary word in parsed
... | nothing
  rewrite originalGammaFailureFromNativeFailure word parsed = refl
... | just (numeral , suffix)
  with Extract.nativeGammaSuccessIsOriginalCanonicalFrame
    word numeral suffix parsed
... | payload , canonical rewrite canonical =
  nativePositiveGammaCanonicalFrameSameOriginal payload suffix
