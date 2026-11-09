{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedSuffixExact where

------------------------------------------------------------------------
-- Karp original signed Elias-gamma decoder: EVERY-WORD suffix equality.
--
-- This pays a real missing P0 branch, including rejected and truncated
-- words, by following the ACTUAL native scanZeros/readPayload path.
-- It does not posit an original signed ℤ to binary-token value equality.
-- Numerical observation is proof-only, not executed by the bit parser.
--
-- Source: DASHI original gamma/zigzag parser, native binary gamma and
-- the all-word unsigned numeric-weld/signed-success proof owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Native
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeAllWordNumericalWeldExact as Numeric
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedAllWordValidityExact as Valid
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Old

suffixBits :
  {A : Set} → Maybe (A × Word.BitWord) → Maybe Word.BitWord
suffixBits nothing = nothing
suffixBits (just (_ , suffix)) = just suffix

-- The native exponent-vector scanner and proof-side numerical scanner
-- make EXACTLY the same suffix choice on every branch.
nativeScanNumericSuffixSame :
  (count : Nat) (word : Word.BitWord) →
  suffixBits (Native.scanZeros count word) ≡
  suffixBits (Numeric.scanNativeNumericView count word)
nativeScanNumericSuffixSame count [] = refl
nativeScanNumericSuffixSame count (false ∷ bits) =
  nativeScanNumericSuffixSame (suc count) bits
nativeScanNumericSuffixSame count (true ∷ bits)
  with Native.readPayload count bits
... | nothing = refl
... | just (payload , suffix) = refl

nativeGammaOriginalSuffixAllWords :
  (word : Word.BitWord) →
  suffixBits (Native.readGammaBinary word)
    ≡ suffixBits (Old.readGamma word)
nativeGammaOriginalSuffixAllWords word =
  trans
    (nativeScanNumericSuffixSame zero word)
    (cong suffixBits
      (Numeric.originalGammaSameAllWordNumericalObservation word))

-- Signed splitting changes only the value representation, not the
-- original suffix. A successful native parse is guaranteed to
-- produce a leading-one numeral by the actual parser's construction.
nativeSignedSuffixEqualsNativeGamma :
  (word : Word.BitWord) →
  suffixBits (Signed.readSignedBinary word)
    ≡ suffixBits (Native.readGammaBinary word)
nativeSignedSuffixEqualsNativeGamma word
  with Native.readGammaBinary word
... | nothing = refl
... | just (numeral , suffix)
  with Valid.scanGammaLeadingOne zero word numeral suffix refl
... | payload , refl
  with Valid.splitLastNonempty true payload
... | (prefix , true) , equation rewrite equation = refl
... | (prefix , false) , equation rewrite equation = refl

originalSignedSuffixEqualsOriginalGamma :
  (word : Word.BitWord) →
  suffixBits (Old.readSignedGamma word)
    ≡ suffixBits (Old.readGamma word)
originalSignedSuffixEqualsOriginalGamma word
  with Old.readGamma word
... | nothing = refl
... | just (value , suffix) = refl

-- P0 signed-gamma SUFFIX equality, all words (including rejection).
-- No all-word equality of native SIGNED VALUES is smuggled into it.
karpNativeSignedGammaSuffixSameOriginal :
  (word : Word.BitWord) →
  suffixBits (Signed.readSignedBinary word)
    ≡ suffixBits (Old.readSignedGamma word)
karpNativeSignedGammaSuffixSameOriginal word =
  trans
    (nativeSignedSuffixEqualsNativeGamma word)
    (trans
      (nativeGammaOriginalSuffixAllWords word)
      (sym (originalSignedSuffixEqualsOriginalGamma word)))


------------------------------------------------------------------------
-- All-word SIGNED NUMERICAL OBSERVATION of the genuine native gamma
-- control path. It follows the existing unsigned all-word numerical
-- equivalence and original zigzag inverse; it does NOT observe the
-- executable SignedMagnitudeBits payload yet. That is the final
-- numerical representation lemma needed by the binary ledger.
------------------------------------------------------------------------

open import Data.Integer.Base using (ℤ)

signedNativeControlNumericView :
  Word.BitWord → Maybe (ℤ × Word.BitWord)
signedNativeControlNumericView word
  with Numeric.scanNativeNumericView zero word
... | nothing = nothing
... | just (number , suffix) =
  just (Old.unzigzag number , suffix)

karpSignedNativeControlNumericViewSameOriginal :
  (word : Word.BitWord) →
  signedNativeControlNumericView word ≡ Old.readSignedGamma word
karpSignedNativeControlNumericViewSameOriginal word
  rewrite Numeric.originalGammaSameAllWordNumericalObservation word = refl
