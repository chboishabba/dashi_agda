{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeAllWordNumericalWeldExact where

------------------------------------------------------------------------
-- K05 N21 ALL-WORD ORIGINAL GAMMA SEMANTICS, NATIVE BINARY RUNTIME.
--
-- Original original-authoritative readGammaZeros reconstructs a unary
-- Nat via pow2, payloadValue and subtraction. The native source
-- readGammaBinary instead returns a binary payload; for each possible
-- malformed or valid original word this theorem shows that the
-- numeric OBSERVATION of the native payload scanner coincides with
-- ORIGINAL readGammaZeros, including the exact remaining suffix.
--
-- Numeric observation is *proof-side only*, not the executable
-- bit-native parser or evidence of unary-runtime polynomiality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Nat.Base using (_∸_)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Old
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Native

-- Interpret the exact k bits read, not their numeric magnitude as a
-- loop bound. k is the original input prefix length.
lowPayloadValue : Nat → Word.BitWord → Nat
lowPayloadValue zero payload = zero
lowPayloadValue (suc k) [] = zero
lowPayloadValue (suc k) (b ∷ payload) =
  Old.bitNat b * Old.pow2 k + lowPayloadValue k payload

numericPayloadResult :
  Nat → Maybe (Word.BitWord × Word.BitWord) →
  Maybe (Nat × Word.BitWord)
numericPayloadResult k nothing = nothing
numericPayloadResult k (just (payload , suffix)) =
  just (lowPayloadValue k payload , suffix)

-- The actual old Nat parser is the numeric observation of the native
-- bit-list payload reader for ALL input words, including truncations.
readPayloadNativeNumericalSameAllWords :
  (k : Nat) (word : Word.BitWord) →
  Old.readLowBits k word ≡
    numericPayloadResult k (Native.readPayload k word)
readPayloadNativeNumericalSameAllWords zero word = refl
readPayloadNativeNumericalSameAllWords (suc k) [] = refl
readPayloadNativeNumericalSameAllWords (suc k) (b ∷ word)
  rewrite readPayloadNativeNumericalSameAllWords k word
  with Native.readPayload k word
... | nothing = refl
... | just (payload , suffix) = refl

-- A numeric view of the exact NATIVE prefix/reader control path.
-- This is NOT the implementation executed by readGammaBinary.
scanNativeNumericView :
  Nat → Word.BitWord → Maybe (Nat × Word.BitWord)
scanNativeNumericView count [] = nothing
scanNativeNumericView count (false ∷ word) =
  scanNativeNumericView (suc count) word
scanNativeNumericView count (true ∷ word)
  with Native.readPayload count word
... | nothing = nothing
... | just (payload , suffix) =
  just ((Old.pow2 count + lowPayloadValue count payload) ∸ suc zero
       , suffix)

-- Actual literal original gamma decoder, ALL WORDS not just
-- canonical images: same accept/reject and the same (Nat,suffix).
scanNativeNumericMatchesOriginal :
  (count : Nat) (word : Word.BitWord) →
  scanNativeNumericView count word
    ≡ Old.readGammaZeros count word
scanNativeNumericMatchesOriginal count [] = refl
scanNativeNumericMatchesOriginal count (false ∷ word) =
  scanNativeNumericMatchesOriginal (suc count) word
scanNativeNumericMatchesOriginal count (true ∷ word)
  rewrite readPayloadNativeNumericalSameAllWords count word
  with Native.readPayload count word
... | nothing = refl
... | just (payload , suffix) = refl

originalGammaSameAllWordNumericalObservation :
  (word : Word.BitWord) →
  scanNativeNumericView zero word ≡ Old.readGamma word
originalGammaSameAllWordNumericalObservation word =
  scanNativeNumericMatchesOriginal zero word

-- This proof does not run the pow2 Nat observation in the executable
-- native parser, nor conflate arithmetic evaluation with bit-machine
-- runtime. Use the original result on the LEFT and the native
-- representation on the RIGHT in the next graph-word interface.
