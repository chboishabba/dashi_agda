{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21ConwayGammaChainCodecExact where

------------------------------------------------------------------------
-- K02: ACTUAL BINARY WIRE REPRESENTATION OF SYMBOLIC CONWAY CHAINS.
--
-- Uses the existing Karp21 Elias-gamma(n+1) encoder/decoder with suffix
-- preservation and the SAME BitWord type as the original E20/N21 codecs.
-- Prefix grammar:
--    gamma(number of chain entries) ++ gamma(entry_1) ++ ...
-- It represents syntax, not the (potentially enormous) evaluated integer.
-- Accepts Nat lists to keep parsing total; the positive Conway-domain
-- predicate is a separate semantic check.
--
-- Source-written: exact-head --safe acceptance still requires parallel_checker.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (_++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
import Data.List.Properties as ListP
open import Relation.Binary.PropositionalEquality using (cong; sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaBinaryRoundTripExact as Round
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Decode
import DASHI.Mathematics.Complexity.Karp21ConwayTotalChainExact as Conway

encodeEntries : List Nat → Word.BitWord
encodeEntries [] = []
encodeEntries (n ∷ ns) =
  Gamma.encodeGammaNat n ++ encodeEntries ns

encodeChainWord : List Nat → Word.BitWord
encodeChainWord entries =
  Gamma.encodeGammaNat (length entries) ++ encodeEntries entries

readEntries :
  Nat → Word.BitWord → Maybe (List Nat × Word.BitWord)
readEntries zero bits = just ([] , bits)
readEntries (suc count) bits with Decode.readGamma bits
... | nothing = nothing
... | just (n , rest) with readEntries count rest
...   | nothing = nothing
...   | just (ns , suffix) = just (n ∷ ns , suffix)

readChainWithSuffix :
  Word.BitWord → Maybe (List Nat × Word.BitWord)
readChainWithSuffix bits with Decode.readGamma bits
... | nothing = nothing
... | just (count , rest) = readEntries count rest

-- Complete-input-only parser: exact count and rejection of trailing data.
decodeChainWord : Word.BitWord → Maybe (List Nat)
decodeChainWord bits with readChainWithSuffix bits
... | nothing = nothing
... | just (xs , []) = just xs
... | just (xs , _ ∷ _) = nothing

readEntriesEncodeSuffix :
  (entries : List Nat) (suffix : Word.BitWord) →
  readEntries (length entries) (encodeEntries entries ++ suffix)
    ≡ just (entries , suffix)
readEntriesEncodeSuffix [] suffix = refl
readEntriesEncodeSuffix (entry ∷ entries) suffix
  rewrite ListP.++-assoc (Gamma.encodeGammaNat entry)
    (encodeEntries entries) suffix
        | Round.gammaReadEncodeSuffix entry (encodeEntries entries ++ suffix)
        | readEntriesEncodeSuffix entries suffix = refl

chainReadEncodeSuffix :
  (entries : List Nat) (suffix : Word.BitWord) →
  readChainWithSuffix (encodeChainWord entries ++ suffix)
    ≡ just (entries , suffix)
chainReadEncodeSuffix entries suffix
  rewrite ListP.++-assoc
    (Gamma.encodeGammaNat (length entries))
    (encodeEntries entries) suffix
        | Round.gammaReadEncodeSuffix (length entries)
            (encodeEntries entries ++ suffix)
        | readEntriesEncodeSuffix entries suffix = refl

chainDecodeEncode :
  (entries : List Nat) →
  decodeChainWord (encodeChainWord entries) ≡ just entries
chainDecodeEncode entries
  rewrite sym (ListP.++-identityʳ (encodeChainWord entries))
        | chainReadEncodeSuffix entries [] = refl

-- Wire length is the sum of actual binary gamma token lengths.
-- This is an exact, useful cost equation, not yet a Turing-machine clock.
entryBitLength : List Nat → Nat
entryBitLength [] = 0
entryBitLength (n ∷ ns) =
  length (Gamma.encodeGammaNat n) + entryBitLength ns

entryWireSizeExact :
  (entries : List Nat) →
  length (encodeEntries entries) ≡ entryBitLength entries
entryWireSizeExact [] = refl
entryWireSizeExact (n ∷ ns)
  rewrite ListP.length-++ (Gamma.encodeGammaNat n)
    {ys = encodeEntries ns}
        | entryWireSizeExact ns = refl

chainWireSizeExact :
  (entries : List Nat) →
  length (encodeChainWord entries) ≡
    length (Gamma.encodeGammaNat (length entries))
    + entryBitLength entries
chainWireSizeExact entries
  rewrite ListP.length-++
    (Gamma.encodeGammaNat (length entries))
    {ys = encodeEntries entries}
        | entryWireSizeExact entries = refl

-- Positive-only typed source language.  No zero-valued chain entry
-- can be constructed through this representation.
parsePositive : List Nat → Maybe (List Conway.Positive)
parsePositive [] = just []
parsePositive (zero ∷ rest) = nothing
parsePositive (suc n ∷ rest) with parsePositive rest
... | nothing = nothing
... | just parsed = just (Conway.positive n ∷ parsed)

parsePositiveEntries :
  (entries : List Conway.Positive) →
  parsePositive (Conway.positiveEntries entries) ≡ just entries
parsePositiveEntries [] = refl
parsePositiveEntries (Conway.positive n ∷ rest)
  rewrite parsePositiveEntries rest = refl

decodePositiveChain : Word.BitWord → Maybe (List Conway.Positive)
decodePositiveChain bits with decodeChainWord bits
... | nothing = nothing
... | just entries = parsePositive entries

positiveChainRoundTrip :
  (entries : List Conway.Positive) →
  decodePositiveChain
    (encodeChainWord (Conway.positiveEntries entries)) ≡ just entries
positiveChainRoundTrip entries
  rewrite chainDecodeEncode (Conway.positiveEntries entries)
        | parsePositiveEntries entries = refl
