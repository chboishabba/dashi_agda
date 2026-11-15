{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedAllWordValidityExact where

------------------------------------------------------------------------
-- K05/E20: ORIGINAL AND NATIVE SIGNED-GAMMA ACCEPTANCE, ALL WORDS.
--
-- The native gamma parser always emits a successor binary numeral
-- beginning in true. Its sign splitter therefore never adds an extra
-- rejection case. This weld covers truncated, malformed, and
-- suffix-bearing input words, not just encoder images.
--
-- The proof reuses the original source-owned signed decoder and the
-- existing all-word unsigned gamma acceptance correspondence.
-- No unary-Nat observation is invoked by the executable native reader.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Maybe.Base using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeAllWordValidityExact as Valid
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Original

-- For any nonempty bit list the selected native splitLast succeeds.
-- The dependent output gives a proof of the exact returned pair.
splitLastNonempty :
  (head : Bool) (tail : Word.BitWord) →
  Σ (Word.BitWord × Bool)
    (λ pair → Signed.splitLast (head ∷ tail) ≡ just pair)
splitLastNonempty head [] = ([] , head) , refl
splitLastNonempty head (b ∷ tail)
  with splitLastNonempty b tail
... | (prefix , last) , equation rewrite equation =
  (head ∷ prefix , last) , refl

-- Every successor numeral produced by the native gamma reader
-- starts with true, hence has a valid native signed representation.
leadingSuccessorSignedValid :
  (tail : Word.BitWord) →
  Valid.accepted (Signed.signMagnitudeFromSuccessorBits (true ∷ tail))
    ≡ true
leadingSuccessorSignedValid tail with splitLastNonempty true tail
... | (prefix , true) , equation rewrite equation = refl
... | (prefix , false) , equation rewrite equation = refl

-- The leading-one property is a theorem about the ACTUAL scanZeros.
scanGammaLeadingOne :
  (seen : Nat) (word numeral suffix : Word.BitWord) →
  Gamma.scanZeros seen word ≡ just (numeral , suffix) →
  Σ Word.BitWord (λ payload → numeral ≡ true ∷ payload)
scanGammaLeadingOne seen [] numeral suffix ()
scanGammaLeadingOne seen (false ∷ rest) numeral suffix agreement =
  scanGammaLeadingOne (suc seen) rest numeral suffix agreement
scanGammaLeadingOne seen (true ∷ rest) numeral suffix agreement
  with Gamma.readPayload seen rest
... | nothing = caseImpossible agreement
  where
    caseImpossible : ∀ {A : Set} {x : A} →
      nothing ≡ just x → Σ Word.BitWord (λ payload → numeral ≡ true ∷ payload)
    caseImpossible ()
... | just (payload , after) with agreement
...   | refl = payload , refl

-- A successful native gamma parse stays successful through sign
-- splitting, for all input words, independently of the numeral size.
nativeSignedAcceptsExactlyNativeGamma :
  (word : Word.BitWord) →
  Valid.accepted (Signed.readSignedBinary word)
    ≡ Valid.accepted (Gamma.readGammaBinary word)
nativeSignedAcceptsExactlyNativeGamma word
  with Gamma.readGammaBinary word
... | nothing = refl
... | just (numeral , suffix)
  with scanGammaLeadingOne zero word numeral suffix refl
...   | payload , refl =
  leadingSuccessorSignedValid payload

originalSignedAcceptsExactlyOriginalGamma :
  (word : Word.BitWord) →
  Valid.accepted (Original.readSignedGamma word)
    ≡ Valid.accepted (Original.readGamma word)
originalSignedAcceptsExactlyOriginalGamma word
  with Original.readGamma word
... | nothing = refl
... | just (value , suffix) = refl

-- Original signed parser and native signed parser have the same
-- acceptance/rejection on EVERY original binary input word.
nativeSignedAcceptsExactlyOriginal :
  (word : Word.BitWord) →
  Valid.accepted (Signed.readSignedBinary word)
    ≡ Valid.accepted (Original.readSignedGamma word)
nativeSignedAcceptsExactlyOriginal word =
  trans
    (nativeSignedAcceptsExactlyNativeGamma word)
    (trans
      (Valid.nativeGammaAcceptsExactlyOriginal word)
      (sym (originalSignedAcceptsExactlyOriginalGamma word)))
