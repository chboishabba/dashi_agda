-- Integration proof candidate: transitive original gamma/graph owner safety
-- not yet kernel certified. Do not assert Agda --safe until its
-- dependency closure is checked under pinned Agda 2.9.
module DASHI.Mathematics.Complexity.Karp21NativeUnsignedEndpointBitReaderExact where

------------------------------------------------------------------------
-- P0-B/F: a GENUINE binary-native endpoint/header gamma reader.
--
-- Unlike original Gamma.readGamma, this executable readGammaNatLE
-- never constructs the potentially exponential unary Nat address.
-- It returns exactly the same original unsigned gamma(n) in LE bits,
-- not the gamma-successor (n+1) bits. No positive-only restriction:
-- endpoints and n,m headers may be zero in the original grammar.
--
-- Source references: actual Native.readGammaBinary parser, actual
-- Positive.predecessorLE ripple borrow; original Gamma.readGamma,
-- canonical all-word frame extraction and numerical predecessor weld.
-- This file proves one-token all-word semantic equivalence. All
-- original graph/certificate/trie/clock transport remains separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.List.Base using (length; reverse; _++_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Data.List.Properties as ListP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Old
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Native
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21GammaBinarySignedPayloadValueCutExact as Frame
import DASHI.Mathematics.Complexity.Karp21NativePositiveThresholdNumericFrameExact as Numerical
import DASHI.Mathematics.Complexity.Karp21SignedGammaAllWordFrameExtractionExact as Extract

-- ACTUAL endpoint/header runtime: zero is accepted, because this is
-- NOT Positive.readPositiveGammaLE (strict only for W threshold).
readGammaNatLE :
  Word.BitWord → Maybe (Word.BitWord × Word.BitWord)
readGammaNatLE word with Native.readGammaBinary word
... | nothing = nothing
... | just (successorBE , suffix) =
  just (Positive.predecessorLE (reverse successorBE) , suffix)

observeUnsignedEndpoint :
  Maybe (Word.BitWord × Word.BitWord) →
  Maybe (Nat × Word.BitWord)
observeUnsignedEndpoint nothing = nothing
observeUnsignedEndpoint (just (numberLE , suffix)) =
  just (Value.valueLE numberLE , suffix)

-- Exact original gamma frame: native endpoint = original gamma(n),
-- including n=0; actual unchanged suffix; no unary Nat in runtime.
unsignedEndpointFrameSameOriginal :
  (payload suffix : Word.BitWord) →
  observeUnsignedEndpoint
    (readGammaNatLE (Frame.originalGammaFrame payload suffix))
    ≡ Old.readGamma (Frame.originalGammaFrame payload suffix)
unsignedEndpointFrameSameOriginal payload suffix
  rewrite Numerical.nativeGammaCanonicalFrame payload suffix
        | Old.readGammaPayloadExact payload suffix
        | Numerical.nativePredecessorValueSameOriginalGamma payload = refl

-- ALL-WORD original numerical and suffix equivalence, including
-- malformed/truncated gamma and arbitrary trailing input.
nativeUnsignedEndpointSameOriginal :
  (word : Word.BitWord) →
  observeUnsignedEndpoint (readGammaNatLE word) ≡ Old.readGamma word
nativeUnsignedEndpointSameOriginal word
  with Native.readGammaBinary word in parsed
... | nothing
  rewrite Numerical.originalGammaFailureFromNativeFailure word parsed =
  refl
... | just (numeral , suffix)
  with Extract.nativeGammaSuccessIsOriginalCanonicalFrame
    word numeral suffix parsed
... | payload , canonical rewrite canonical =
  unsignedEndpointFrameSameOriginal payload suffix

-- The binary predecessor NEVER grows its bit-width: every output
-- header/endpoint register is bounded by its already-read successor
-- digits, independently of exponentially large numerical value.
predecessorPreservesBitWidth :
  (bits : Word.BitWord) →
  length (Positive.predecessorLE bits) ≡ length bits
predecessorPreservesBitWidth [] = refl
predecessorPreservesBitWidth (true ∷ rest) = refl
predecessorPreservesBitWidth (false ∷ rest) =
  cong suc (predecessorPreservesBitWidth rest)

unsignedEndpointFrameBitWidth :
  (payload suffix : Word.BitWord) →
  readGammaNatLE (Frame.originalGammaFrame payload suffix)
    ≡ just
      (Positive.predecessorLE (reverse (true ∷ payload)) , suffix)
unsignedEndpointFrameBitWidth payload suffix
  rewrite Numerical.nativeGammaCanonicalFrame payload suffix = refl

unsignedEndpointResultWidth :
  (payload : Word.BitWord) →
  length (Positive.predecessorLE (reverse (true ∷ payload)))
    ≡ suc (length payload)
unsignedEndpointResultWidth payload =
  trans
    (predecessorPreservesBitWidth (reverse (true ∷ payload)))
    (ListP.length-reverse (true ∷ payload))
