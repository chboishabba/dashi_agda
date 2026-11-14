{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21SignedGammaNativeItemStreamExact where

------------------------------------------------------------------------
-- Original E20 / Karp signed partition word: all-word native item
-- stream NUMERICAL correspondence, not only a single signed token.
--
-- Reuses the actual source readSignedGamma and readSignedItems grammar
-- and the new all-word SignedMagnitudeBits observation equality.
-- Recursion follows the ORIGINAL source-specified count, not a new
-- partition language. The Nat count here is the original proof-side
-- control path: a bit-native count runtime and a physical clock are
-- still separate obligations.
--
-- All truncations, negative values, sign-zero and suffixes are covered.
-- Original attribution: Elias gamma, Karp 1972 and DASHI E20 owner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Integer.Base using (ℤ)
open import Relation.Binary.PropositionalEquality using (cong)
import Data.Nat.Properties as NatP
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Old
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Native
import DASHI.Mathematics.Complexity.Karp21SignedGammaNativeOriginalValueExact as Value

-- Each token is produced by the ACTUAL executable native binary reader;
-- its value is observed through the source-owned observeNativeSigned.
-- ℤ conversion is intentionally proof-side only, to test same-object
-- original stream semantics before the bit-runtime certification.
readNativeObservedItems :
  Nat → Word.BitWord → Maybe (List ℤ × Word.BitWord)
readNativeObservedItems zero bits = just ([] , bits)
readNativeObservedItems (suc count) bits
  with Value.observeNativeSigned (Native.readSignedBinary bits)
... | nothing = nothing
... | just (value , suffix)
  with readNativeObservedItems count suffix
... | nothing = nothing
... | just (values , after) =
  just (value ∷ values , after)

-- Same success/rejection, full SIGNED values, and final suffix for
-- arbitrary counts and source words. No encoder-image premise.
nativeObservedItemsSameOriginal :
  (count : Nat) (bits : Word.BitWord) →
  readNativeObservedItems count bits ≡ Old.readSignedItems count bits
nativeObservedItemsSameOriginal zero bits = refl
nativeObservedItemsSameOriginal (suc count) bits
  rewrite Value.karpNativeSignedTokenValueMatchesOriginal bits
  with Old.readSignedGamma bits
... | nothing = refl
... | just (value , suffix)
  rewrite nativeObservedItemsSameOriginal count suffix
  with Old.readSignedItems count suffix
... | nothing = refl
... | just (values , after) = refl

-- Keep the ORIGINAL count parser, length budget, and strict trailing
-- suffix policy. Only replace the original signed items with the
-- observed actual-native binary token stream.
decodePartitionViaNativeObservedItems :
  Word.BitWord → Maybe (List ℤ)
decodePartitionViaNativeObservedItems bits
  with Old.readGamma bits
... | nothing = nothing
... | just (count , rest)
  with NatP._≤?_ count (length rest)
... | no _ = nothing
... | yes _
  with readNativeObservedItems count rest
... | nothing = nothing
... | just (values , []) = just values
... | just (values , _ ∷ _) = nothing

-- All original partition words including malformed/trailing garbage;
-- the same source-set decision, same signed value list.
nativeObservedPartitionSameOriginal :
  (bits : Word.BitWord) →
  decodePartitionViaNativeObservedItems bits ≡ Old.decodePartitionWord bits
nativeObservedPartitionSameOriginal bits
  with Old.readGamma bits
... | nothing = refl
... | just (count , rest)
  with NatP._≤?_ count (length rest)
... | no _ = refl
... | yes _
  rewrite nativeObservedItemsSameOriginal count rest
  with Old.readSignedItems count rest
... | nothing = refl
... | just (values , []) = refl
... | just (values , _ ∷ _) = refl
