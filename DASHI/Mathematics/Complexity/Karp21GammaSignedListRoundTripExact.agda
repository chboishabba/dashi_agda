{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21GammaSignedListRoundTripExact where

------------------------------------------------------------------------
-- KARP E20: ACTUAL SIGNED PARTITION INPUT WORD ROUNDTRIP.
--
-- This is the exact gamma(n+1)/zigzag List ℤ source wire format:
-- gamma(count) ++ concatenated gamma(zigzag(value_i)).
-- It reuses the same literal Agda decoder from the existing Python
-- codec, and the same binary gamma numeral encoder.
--
-- Every input list is accepted, including negative integers, zeros
-- and repeated entries. No list deduplication, arbitrary markers,
-- or user-supplied codec roundtrip fields are used.
--
-- Historical sources: Elias gamma; signed zigzag; Karp 1972;
-- original DASHI source code and Agda standard binary owners.
-- Source-written until independent Agda kernel acceptance.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; z≤n; s≤s; _∸_)
open import Data.Nat.Properties as NatP
open import Data.List.Base using (List; []; _∷_; _++_; length)
import Data.List.Properties as ListP
open import Data.Product using (Σ; _,_)
open import Data.Maybe.Base using (just)
open import Data.Empty using (⊥-elim)
open import Data.Integer.Base using (ℤ)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)
import Data.Nat.Binary.Base as Bin

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact as Enc
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Dec
import DASHI.Mathematics.Complexity.Karp21GammaBinaryRoundTripExact as Gamma

encodeSignedGammaPure : ℤ → Word.BitWord
encodeSignedGammaPure value =
  Enc.encodeGammaNat (Dec.zigzag value)

encodeSignedValuesPure : List ℤ → Word.BitWord
encodeSignedValuesPure [] = []
encodeSignedValuesPure (value ∷ rest) =
  encodeSignedGammaPure value ++ encodeSignedValuesPure rest

encodePartitionWordPure : List ℤ → Word.BitWord
encodePartitionWordPure values =
  Enc.encodeGammaNat (length values) ++ encodeSignedValuesPure values

readSignedGammaEncodeSuffix :
  (value : ℤ) (suffix : Word.BitWord) →
  Dec.readSignedGamma (encodeSignedGammaPure value ++ suffix)
    ≡ just (value , suffix)
readSignedGammaEncodeSuffix value suffix
  rewrite Gamma.gammaReadEncodeSuffix (Dec.zigzag value) suffix
        | Dec.unzigzagZigzag value =
  refl

readSignedItemsEncodeSuffix :
  (values : List ℤ) (suffix : Word.BitWord) →
  Dec.readSignedItems (length values)
    (encodeSignedValuesPure values ++ suffix)
    ≡ just (values , suffix)
readSignedItemsEncodeSuffix [] suffix = refl
readSignedItemsEncodeSuffix (value ∷ rest) suffix
  rewrite ListP.++-assoc
            (encodeSignedGammaPure value)
            (encodeSignedValuesPure rest)
            suffix
        | readSignedGammaEncodeSuffix value
            (encodeSignedValuesPure rest ++ suffix)
        | readSignedItemsEncodeSuffix rest suffix =
  refl

------------------------------------------------------------------------
-- One bit per signed value is a genuine lower bound on the actual
-- encoded source list, not a source-level oracle or a length field.
-- It pays the original decodePartitionWord 'count ≤ restLength' guard.
------------------------------------------------------------------------

zeroPrefixAppendNonempty :
  (k : Nat) (b : Bin.ℕᵇ) →
  suc zero ≤ length
    (Enc.zeroPrefix k ++ Enc.successorBits b)
zeroPrefixAppendNonempty zero b =
  subst
    (λ encodedLength → suc zero ≤ encodedLength)
    (sym (Enc.successorBitsLength b))
    (s≤s z≤n)
zeroPrefixAppendNonempty (suc k) b = s≤s z≤n

gammaNatHasBit :
  (n : Nat) →
  suc zero ≤ length (Enc.encodeGammaNat n)
gammaNatHasBit n =
  zeroPrefixAppendNonempty
    (length (Enc.successorBits (Bin.fromℕ n)) ∸ suc zero)
    (Bin.fromℕ n)

signedListWireLengthLower :
  (values : List ℤ) →
  length values ≤ length (encodeSignedValuesPure values)
signedListWireLengthLower [] = z≤n
signedListWireLengthLower (value ∷ rest)
  rewrite ListP.length-++ (encodeSignedGammaPure value) =
  NatP.+-mono-≤
    (gammaNatHasBit (Dec.zigzag value))
    (signedListWireLengthLower rest)

-- This is the SAME decoder, not a parallel version using a trivial
-- answer for a syntactically valid List of signed numbers.
partitionWordDecodeEncode :
  (values : List ℤ) →
  Dec.decodePartitionWord (encodePartitionWordPure values)
    ≡ just values
partitionWordDecodeEncode values
  rewrite Gamma.gammaReadEncodeSuffix
    (length values) (encodeSignedValuesPure values)
  with NatP._≤?_ (length values)
    (length (encodeSignedValuesPure values))
... | no impossible =
  ⊥-elim (impossible (signedListWireLengthLower values))
... | yes _ rewrite readSignedItemsEncodeSuffix values [] = refl
