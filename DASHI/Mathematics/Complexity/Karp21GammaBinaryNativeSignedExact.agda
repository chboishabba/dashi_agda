{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact where

------------------------------------------------------------------------
-- K05/E20/N21: BINARY-NATIVE ZIGZAG SIGN+MAGNITUDE REPRESENTATION.
--
-- The original zigzag Nat code n is represented by the source Elias
-- gamma payload for n+1. The binary last bit of n+1 determines sign:
--   last=1: zigzag n even, nonnegative original integer
--   last=0: zigzag n odd, negative original integer
-- The preceding binary bits carry floor((n+1)/2), the unsigned
-- magnitude. No full n=2^k sized unary Nat or Peano half/even pass.
--
-- Uses the ACTUAL previous source gamma binary-native parser.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (_++_; length)
open import Data.Product using (_×_; _,_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (cong)
import Data.Nat.Binary.Base as Bin

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact as Enc
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Raw
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Old

data SignedMagnitudeBits : Set where
  positive : Word.BitWord → SignedMagnitudeBits
  negative : Word.BitWord → SignedMagnitudeBits

splitLast :
  Word.BitWord → Maybe (Word.BitWord × Bool)
splitLast [] = nothing
splitLast (b ∷ []) = just ([] , b)
splitLast (b ∷ b2 ∷ rest)
  with splitLast (b2 ∷ rest)
... | nothing = nothing
... | just (prefix , final) = just (b ∷ prefix , final)

splitLastAppendExact :
  (prefix : Word.BitWord) (last : Bool) →
  splitLast (prefix ++ (last ∷ []))
    ≡ just (prefix , last)
splitLastAppendExact [] last = refl
splitLastAppendExact (b ∷ prefix) last
  rewrite splitLastAppendExact prefix last = refl

signMagnitudeFromSuccessorBits :
  Word.BitWord → Maybe SignedMagnitudeBits
signMagnitudeFromSuccessorBits bits with splitLast bits
... | nothing = nothing
... | just (magnitude , true) = just (positive magnitude)
... | just (magnitude , false) = just (negative magnitude)

readSignedBinary :
  Word.BitWord → Maybe (SignedMagnitudeBits × Word.BitWord)
readSignedBinary word with Raw.readGammaBinary word
... | nothing = nothing
... | just (bits , suffix)
  with signMagnitudeFromSuccessorBits bits
...   | nothing = nothing
...   | just signed = just (signed , suffix)

-- Output is literally derived from the original Karp Elias-gamma
-- encoder, not a substitute decoder or a new sign convention.
readSignedOriginalGammaEncodedExact :
  (n : Nat) (suffix : Word.BitWord) →
  readSignedBinary (Enc.encodeGammaNat n ++ suffix)
    ≡ justResult
        (signMagnitudeFromSuccessorBits
          (Enc.successorBits (Bin.fromℕ n)))
        suffix
  where
    justResult :
      Maybe SignedMagnitudeBits → Word.BitWord →
      Maybe (SignedMagnitudeBits × Word.BitWord)
    justResult nothing rest = nothing
    justResult (just signed) rest = just (signed , rest)
readSignedOriginalGammaEncodedExact n suffix
  rewrite Raw.gammaOriginalEncodeNativeSuffix n suffix = refl

-- Inspection work for splitting a nonempty big-endian bitword.
-- The gamma bitreader's original all-input linear work is separate.
splitLastInspectionWork : Word.BitWord → Nat
splitLastInspectionWork [] = 1
splitLastInspectionWork (_ ∷ []) = 1
splitLastInspectionWork (_ ∷ _ ∷ rest) =
  suc (splitLastInspectionWork (true ∷ rest))

-- A bit-native value/representation correspondence over ALL words
-- still needs an all-word numerical weld to Old.readSignedGamma.
