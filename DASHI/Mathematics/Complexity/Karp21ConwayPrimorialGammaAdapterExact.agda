module DASHI.Mathematics.Complexity.Karp21ConwayPrimorialGammaAdapterExact where

------------------------------------------------------------------------
-- K02 factor-vector adapter for the ORIGINAL primorial four-prime carrier.
-- Importing a legacy non---safe source owner is intentionally separated
-- from the transitive-safe Conway gamma-chain codec.
-- This maps a finite exponent vector to its binary *description*,
-- never treating it as a Conway-evaluated numeric value.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (_++_; length)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.Maybe.Base using (Maybe; just; nothing)

import DASHI.Foundations.PrimorialFactorAddressConcrete as Prime
import Ontology.GodelLattice as Godel
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21ConwayGammaChainCodecExact as Chain

factorEntries : Prime.PrimorialDigits4 → List Nat
factorEntries digits =
  Prime.digit2 digits ∷
  Prime.digit3 digits ∷
  Prime.digit5 digits ∷
  Prime.digit7 digits ∷ []

encodeFactorWord : Prime.PrimorialDigits4 → Word.BitWord
encodeFactorWord digits = Chain.encodeChainWord (factorEntries digits)

decodeFactorWord : Word.BitWord → Maybe Prime.PrimorialDigits4
decodeFactorWord bits with Chain.decodeChainWord bits
... | just (a ∷ b ∷ c ∷ d ∷ []) =
  just (Prime.primorialDigits4 a b c d)
... | _ = nothing

factorDecodeEncode :
  (digits : Prime.PrimorialDigits4) →
  decodeFactorWord (encodeFactorWord digits) ≡ just digits
factorDecodeEncode (Prime.primorialDigits4 a b c d)
  rewrite Chain.chainDecodeEncode (a ∷ b ∷ c ∷ d ∷ []) = refl

-- A witness demonstrating why address-decoding and exponent product
-- are separate semantic interpretations of the SAME vector.
exampleAddress : Prime.PrimorialDigits4
exampleAddress = Prime.primorialDigits4 0 0 4 0

addressIsTwentyFour : Prime.primorialDecode4 exampleAddress ≡ 24
addressIsTwentyFour = refl

factorProductIsSixTwoFive :
  Prime.primeExponentProduct4 exampleAddress ≡ 625
factorProductIsSixTwoFive = refl

------------------------------------------------------------------------
-- SSP15: reuse the original fifteen-prime exponent lattice. The
-- bitword is strictly lossless as a vector with ordered prime slots.
-- This is not an assertion that numeric scalar Gödel encoding is cheap.
------------------------------------------------------------------------

factor15Entries : Godel.FactorVec → List Nat
factor15Entries (Godel.v15 a b c d e f g h i j k l m n o) =
  a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷
  k ∷ l ∷ m ∷ n ∷ o ∷ []

encodeFactor15Word : Godel.FactorVec → Word.BitWord
encodeFactor15Word factors = Chain.encodeChainWord (factor15Entries factors)

decodeFactor15Word : Word.BitWord → Maybe Godel.FactorVec
decodeFactor15Word bits with Chain.decodeChainWord bits
... | just (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷
            j ∷ k ∷ l ∷ m ∷ n ∷ o ∷ []) =
  just (Godel.v15 a b c d e f g h i j k l m n o)
... | _ = nothing

factor15DecodeEncode :
  (factors : Godel.FactorVec) →
  decodeFactor15Word (encodeFactor15Word factors) ≡ just factors
factor15DecodeEncode (Godel.v15 a b c d e f g h i j k l m n o)
  rewrite Chain.chainDecodeEncode
    (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ j ∷
     k ∷ l ∷ m ∷ n ∷ o ∷ []) = refl

------------------------------------------------------------------------
-- Fixed-four and SSP15 prime vectors inherit the exact canonical
-- gamma chain bit length, injectivity, and raw-bit prefix exclusion.
------------------------------------------------------------------------

factor4WireLength :
  (digits : Prime.PrimorialDigits4) →
  length (encodeFactorWord digits) ≡
    length (Chain.Gamma.encodeGammaNat (length (factorEntries digits)))
    + Chain.entryBitLength (factorEntries digits)
factor4WireLength digits =
  Chain.chainWireSizeExact (factorEntries digits)

factor15WireLength :
  (factors : Godel.FactorVec) →
  length (encodeFactor15Word factors) ≡
    length (Chain.Gamma.encodeGammaNat (length (factor15Entries factors)))
    + Chain.entryBitLength (factor15Entries factors)
factor15WireLength factors =
  Chain.chainWireSizeExact (factor15Entries factors)

factor4EncodeInjective :
  (a b : Prime.PrimorialDigits4) →
  encodeFactorWord a ≡ encodeFactorWord b →
  a ≡ b
factor4EncodeInjective a b equal
  with factorDecodeEncode a | factorDecodeEncode b
... | left | right =
  justInject
    (cong decodeFactorWord equal)
  where
    justInject : ∀ {x y : Prime.PrimorialDigits4} →
      just x ≡ just y → x ≡ y
    justInject refl = refl

factor15EncodeInjective :
  (a b : Godel.FactorVec) →
  encodeFactor15Word a ≡ encodeFactor15Word b →
  a ≡ b
factor15EncodeInjective a b equal =
  justInject
    (cong decodeFactor15Word equal)
  where
    justInject : ∀ {x y : Godel.FactorVec} →
      just x ≡ just y → x ≡ y
    justInject refl = refl

factor4NoProperBinaryPrefix :
  (a b : Prime.PrimorialDigits4)
  (suffix : Word.BitWord) →
  encodeFactorWord a ++ suffix ≡ encodeFactorWord b →
  suffix ≡ []
factor4NoProperBinaryPrefix a b suffix =
  Chain.chainFullBinaryNoProperPrefix
    (factorEntries a) (factorEntries b) suffix

factor15NoProperBinaryPrefix :
  (a b : Godel.FactorVec)
  (suffix : Word.BitWord) →
  encodeFactor15Word a ++ suffix ≡ encodeFactor15Word b →
  suffix ≡ []
factor15NoProperBinaryPrefix a b suffix =
  Chain.chainFullBinaryNoProperPrefix
    (factor15Entries a) (factor15Entries b) suffix
