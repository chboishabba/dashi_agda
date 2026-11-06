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
