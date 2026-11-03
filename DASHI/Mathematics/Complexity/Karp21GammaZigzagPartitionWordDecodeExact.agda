{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact where

------------------------------------------------------------------------
-- E20 WIRE CODEC: ACTUAL PYTHON PARTITION FORMAT, SOURCE DECODING.
--
-- Prior executable owner:
--   scripts/karp21_signed_cut_binary_codec.py
--       gamma_nat(n) = 0^k ++ binary(n + 1), k = bitlen(n + 1) - 1
--       zigzag(+n) = 2n; zigzag(-(n+1)) = 2n+1
--       source = gamma(count) ++ concat(gamma(zigzag(value_i)))
--
-- This is a literal strict bit parser, not a total default-to-zero
-- decoder. It rejects truncated gamma words, too many declared items,
-- and every trailing suffix.  It never allocates a certificate or an
-- array indexed by the magnitude of an integer label.
--
-- This module supplies source DECODE and exact zigzag inverse, not the
-- missing encoder/decoder roundtrip or polynomial machine clock.
-- Source ownership: Karp (1972); DASHI existing Python E20 codec.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_∸_)
open import Data.Nat.Properties as NatP using (_≤?_)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.Product using (_×_; _,_)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import Data.Nat.Properties as Arithmetic

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word

------------------------------------------------------------------------
-- The direct natural-number zigzag bijection: no sign bit lost at 0.
------------------------------------------------------------------------

twice : Nat → Nat
twice zero = zero
twice (suc n) = suc (suc (twice n))

half : Nat → Nat
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

even : Nat → Bool
even zero = true
even (suc zero) = false
even (suc (suc n)) = even n

zigzag : ℤ → Nat
zigzag (+ n) = twice n
zigzag (-[1+ n ]) = suc (twice n)

unzigzag : Nat → ℤ
unzigzag n with even n
... | true = + (half n)
... | false = -[1+ half n ]

halfTwice : (n : Nat) → half (twice n) ≡ n
halfTwice zero = refl
halfTwice (suc n) = cong suc (halfTwice n)

evenTwice : (n : Nat) → even (twice n) ≡ true
evenTwice zero = refl
evenTwice (suc n) = evenTwice n

halfOddTwice : (n : Nat) → half (suc (twice n)) ≡ n
halfOddTwice zero = refl
halfOddTwice (suc n) = cong suc (halfOddTwice n)

oddTwice : (n : Nat) → even (suc (twice n)) ≡ false
oddTwice zero = refl
oddTwice (suc n) = oddTwice n

unzigzagZigzag : (z : ℤ) → unzigzag (zigzag z) ≡ z
unzigzagZigzag (+ n)
  rewrite evenTwice n | halfTwice n = refl
unzigzagZigzag (-[1+ n ])
  rewrite oddTwice n | halfOddTwice n = refl

------------------------------------------------------------------------
-- Reverse direction, required for a genuine zigzag integer/Nat
-- bijection on the canonical gamma numeral representation.
-- The two parity branches reconstruct the original Nat code exactly.
------------------------------------------------------------------------

evenHalfExact :
  (n : Nat) →
  even n ≡ true →
  twice (half n) ≡ n
evenHalfExact zero observed = refl
evenHalfExact (suc zero) ()
evenHalfExact (suc (suc n)) observed =
  cong suc (cong suc (evenHalfExact n observed))

oddHalfExact :
  (n : Nat) →
  even n ≡ false →
  suc (twice (half n)) ≡ n
oddHalfExact zero ()
oddHalfExact (suc zero) observed = refl
oddHalfExact (suc (suc n)) observed =
  cong suc (cong suc (oddHalfExact n observed))

zigzagUnzigzag : (n : Nat) → zigzag (unzigzag n) ≡ n
zigzagUnzigzag n with even n
... | true = evenHalfExact n refl
... | false = oddHalfExact n refl


------------------------------------------------------------------------
-- Exactly k low-order binary payload bits, high-to-low on the wire.
-- This is the post-leading-1 section of an Elias-gamma natural.
------------------------------------------------------------------------

pow2 : Nat → Nat
pow2 zero = suc zero
pow2 (suc k) = (suc (suc zero)) * pow2 k

bitNat : Bool → Nat
bitNat false = zero
bitNat true = suc zero

readLowBits :
  Nat → Word.BitWord → Maybe (Nat × Word.BitWord)
readLowBits zero rest = just (zero , rest)
readLowBits (suc k) [] = nothing
readLowBits (suc k) (bit ∷ rest)
  with readLowBits k rest
... | nothing = nothing
... | just (low , suffix) =
  just (bitNat bit * pow2 k + low , suffix)

------------------------------------------------------------------------
-- The source-owned payload decoder is EXACT and suffix-preserving.
-- These are equalities about the literal executable bit parser.
------------------------------------------------------------------------

payloadValue : Word.BitWord → Nat
payloadValue [] = zero
payloadValue (bit ∷ bits) =
  bitNat bit * pow2 (length bits) + payloadValue bits

readLowBitsAppendExact :
  (payload suffix : Word.BitWord) →
  readLowBits (length payload) (payload ++ suffix)
    ≡ just (payloadValue payload , suffix)
readLowBitsAppendExact [] suffix = refl
readLowBitsAppendExact (bit ∷ bits) suffix
  rewrite readLowBitsAppendExact bits suffix = refl

-- Prefix compression does not inspect, alter or discard the suffix.
-- Retaining a general starting zero count makes the proof reusable
-- inside graph-edge, source-list and threshold decoders.
zeroPrefix : Nat → Word.BitWord
zeroPrefix zero = []
zeroPrefix (suc n) = false ∷ zeroPrefix n

readGammaZeroPrefixExact :
  (seen zeros : Nat)
  (suffix : Word.BitWord) →
  readGammaZeros seen
    (zeroPrefix zeros ++ (true ∷ suffix))
    ≡ readGammaZeros (seen + zeros) (true ∷ suffix)
readGammaZeroPrefixExact seen zero suffix
  rewrite Arithmetic.+-identityʳ seen = refl
readGammaZeroPrefixExact seen (suc zeros) suffix
  rewrite Arithmetic.+-suc seen zeros =
  readGammaZeroPrefixExact (suc seen) zeros suffix

-- This is the exact decoded number of an arbitrary well-formed
-- gamma header with k payload bits. The numeric "same n" theorem
-- still needs the separate binary numeral VALUE identity.
readGammaPayloadExact :
  (payload suffix : Word.BitWord) →
  readGamma
    (zeroPrefix (length payload)
      ++ (true ∷ (payload ++ suffix)))
    ≡ just
      ((pow2 (length payload) + payloadValue payload) ∸ suc zero
      , suffix)
readGammaPayloadExact payload suffix
  rewrite readGammaZeroPrefixExact zero (length payload)
    (payload ++ suffix)
        | readLowBitsAppendExact payload suffix =
  refl

------------------------------------------------------------------------
-- The literal gamma(n + 1) decoder.
-- Zero prefix count k -> leading 1 -> exactly k payload bits.
-- A naked leading zero or an incomplete payload is rejected.
------------------------------------------------------------------------

readGammaZeros :
  Nat → Word.BitWord → Maybe (Nat × Word.BitWord)
readGammaZeros zeros [] = nothing
readGammaZeros zeros (false ∷ rest) =
  readGammaZeros (suc zeros) rest
readGammaZeros zeros (true ∷ rest)
  with readLowBits zeros rest
... | nothing = nothing
... | just (low , suffix) =
  just ((pow2 zeros + low) ∸ suc zero , suffix)

readGamma : Word.BitWord → Maybe (Nat × Word.BitWord)
readGamma = readGammaZeros zero

readSignedGamma :
  Word.BitWord → Maybe (ℤ × Word.BitWord)
readSignedGamma word with readGamma word
... | nothing = nothing
... | just (value , rest) =
  just (unzigzag value , rest)

------------------------------------------------------------------------
-- Every signed element consumes a gamma word. The count is checked
-- against the total number of REMAINING bits before recursion.
------------------------------------------------------------------------

readSignedItems :
  Nat → Word.BitWord → Maybe (List ℤ × Word.BitWord)
readSignedItems zero word = just ([] , word)
readSignedItems (suc count) word
  with readSignedGamma word
... | nothing = nothing
... | just (value , afterHead)
  with readSignedItems count afterHead
...   | nothing = nothing
...   | just (items , suffix) =
  just (value ∷ items , suffix)

decodePartitionWord : Word.BitWord → Maybe (List ℤ)
decodePartitionWord word with readGamma word
... | nothing = nothing
... | just (count , rest)
  with NatP._≤?_ count (length rest)
...   | no _ = nothing
...   | yes _ with readSignedItems count rest
...     | nothing = nothing
...     | just (parts , []) = just parts
...     | just (parts , _ ∷ _) = nothing

------------------------------------------------------------------------
-- Literal small-word fixtures on the SAME gamma(n+1)/zigzag contract.
-- These equality proofs evaluate the actual decoder definition.
------------------------------------------------------------------------

gammaZeroDecodes :
  readGamma (true ∷ [])
    ≡ just (zero , [])
gammaZeroDecodes = refl

gammaOneDecodes :
  readGamma (false ∷ true ∷ false ∷ [])
    ≡ just (suc zero , [])
gammaOneDecodes = refl

gammaTwoDecodes :
  readGamma (false ∷ true ∷ true ∷ [])
    ≡ just (suc (suc zero) , [])
gammaTwoDecodes = refl

gammaTruncationRejected :
  readGamma (false ∷ true ∷ [])
    ≡ nothing
gammaTruncationRejected = refl

emptyPartitionWordDecodes :
  decodePartitionWord (true ∷ []) ≡ just []
emptyPartitionWordDecodes = refl

oneZeroPartitionWordDecodes :
  decodePartitionWord
    (false ∷ true ∷ false ∷ true ∷ [])
    ≡ just ((+ zero) ∷ [])
oneZeroPartitionWordDecodes = refl

twoOppositeSignedWordDecodes :
  decodePartitionWord
    (false ∷ true ∷ true ∷
     false ∷ true ∷ true ∷
     false ∷ true ∷ false ∷ [])
    ≡ just ((+ (suc zero)) ∷ (-[1+ zero ]) ∷ [])
twoOppositeSignedWordDecodes = refl

trailingPartitionBitRejected :
  decodePartitionWord (true ∷ false ∷ []) ≡ nothing
trailingPartitionBitRejected = refl
