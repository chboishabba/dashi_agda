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
