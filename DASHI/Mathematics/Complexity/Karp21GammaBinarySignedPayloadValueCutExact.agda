{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21GammaBinarySignedPayloadValueCutExact where

------------------------------------------------------------------------
-- Karp original signed Elias gamma: real encoded-frame P0 reduction.
--
-- Fix an arbitrary original gamma payload p = prefix ++ [last].
-- On the EXACT SAME WIRE WORD, prove:
--  * actual binary-native signed reader returns the literal signed
--    magnitude token, preserving the EXACT suffix;
--  * original signed-ℤ reader returns the original unzigzag of the
--    source's actual pow2/payloadValue expression, same suffix.
--
-- This isolates the genuinely missing bit-number arithmetic theorem
-- without pretending an observation of unsigned gamma is its proof.
-- Input prefix and suffix are arbitrary; no magnitude bound or
-- synthetic parser. Empty-payload gamma(0) is handled separately.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; suc; zero; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.List.Base using (length; _++_)
open import Data.Nat.Base using (_∸_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe.Base using (Maybe; just)
open import Data.Integer.Base using (ℤ)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativeSignedExact as Signed
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Native
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Original

originalGammaFrame :
  Word.BitWord → Word.BitWord → Word.BitWord
originalGammaFrame payload suffix =
  Original.zeroPrefix (length payload) ++
    (true ∷ (payload ++ suffix))

signedTokenFromLast :
  Word.BitWord → Bool → Signed.SignedMagnitudeBits
signedTokenFromLast prefix true =
  Signed.positive (true ∷ prefix)
signedTokenFromLast prefix false =
  Signed.negative (true ∷ prefix)

-- The source's actual readSignedBinary, not an invented value function.
karpNativeSignedPayloadFrameExact :
  (prefix suffix : Word.BitWord) (last : Bool) →
  Signed.readSignedBinary
    (originalGammaFrame (prefix ++ (last ∷ [])) suffix)
  ≡ just (signedTokenFromLast prefix last , suffix)
karpNativeSignedPayloadFrameExact prefix suffix true
  rewrite Native.readGammaBinaryPayloadExact
    (prefix ++ (true ∷ [])) suffix
        | Signed.splitLastAppendExact (true ∷ prefix) true = refl
karpNativeSignedPayloadFrameExact prefix suffix false
  rewrite Native.readGammaBinaryPayloadExact
    (prefix ++ (false ∷ [])) suffix
        | Signed.splitLastAppendExact (true ∷ prefix) false = refl

-- Actual original gamma readSignedGamma, with original zigzag number.
originalPayloadSignedNat : Word.BitWord → Nat
originalPayloadSignedNat payload =
  (Original.pow2 (length payload) +
    Original.payloadValue payload) ∸ suc zero

karpOriginalSignedPayloadFrameExact :
  (payload suffix : Word.BitWord) →
  Original.readSignedGamma (originalGammaFrame payload suffix)
    ≡ just (Original.unzigzag (originalPayloadSignedNat payload) , suffix)
karpOriginalSignedPayloadFrameExact payload suffix
  rewrite Original.readGammaPayloadExact payload suffix = refl

-- Both source parsers agree on their exact gamma suffix and have
-- explicitly computed value representations on every nonempty payload.
-- The outstanding arithmetic lemma is precisely:
-- interpretSignedMagnitude (signedTokenFromLast prefix last)
--   ≡ Original.unzigzag
--       (originalPayloadSignedNat (prefix ++ last ∷ [])).
-- It must use the ACTUAL Value.valueLE (reverse magnitude) and
-- Old.unzigzag rather than a new normative numerical representation.

karpGammaZeroNativeTokenExact :
  Signed.readSignedBinary
    (originalGammaFrame [] [])
  ≡ just (Signed.positive [] , [])
karpGammaZeroNativeTokenExact = refl

karpGammaZeroOriginalSignedExact :
  Original.readSignedGamma
    (originalGammaFrame [] [])
  ≡ just (Original.unzigzag zero , [])
karpGammaZeroOriginalSignedExact = refl
