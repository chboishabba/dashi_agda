{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21GammaBinaryRoundTripExact where

------------------------------------------------------------------------
-- P1: FIRST FULL ORIGINAL GAMMA(n+1) NUMERIC ROUNDTRIP.
--
-- Same-object code path:
--   Karp21GammaBinaryGoldenCoreExact.encodeGammaNat
--     -> Karp21GammaZigzagPartitionWordDecodeExact.readGamma
--     -> same original Nat, same unconsumed suffix.
--
-- Reuse the exact binary numeral source-owner lemmas:
--   BinP.toℕ-fromℕ; successorBitsNumericValue;
--   readGammaPayloadExact; gammaPrefixExactlyBinarySize.
-- No alternative tokenizer, unary exponential encoder, or oracle.
--
-- This completes a source-written gammaReadEncodeRoundTrip theorem.
-- Agda kernel acceptance and polynomial bit-machine time remain OPEN.
-- Historical source: Elias gamma; standard-library binary conversion;
-- Karp (1972); original DASHI signed PARTITION codec.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_∸_)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Product using (Σ; _,_)
open import Data.Maybe.Base using (just)
import Data.List.Properties as ListP
import Data.Nat.Properties as NatP
import Data.Nat.Binary.Base as Bin
import Data.Nat.Binary.Properties as BinP
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact as Enc
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Dec
import DASHI.Mathematics.Complexity.Karp21GammaBinaryPayloadValueExact as Val

-- The two original owners used identical recursive zero-prefix
-- constructions but distinct constants. Pay extensional identity
-- explicitly, rather than assuming their implementations are
-- judgmentally equal at a variable natural-number index.
zeroPrefixSameObject :
  (n : Nat) → Enc.zeroPrefix n ≡ Dec.zeroPrefix n
zeroPrefixSameObject zero = refl
zeroPrefixSameObject (suc n) =
  cong (false ∷_) (zeroPrefixSameObject n)

successorPayloadLength :
  (b : Bin.ℕᵇ) (payload : Word.BitWord) →
  Enc.successorBits b ≡ true ∷ payload →
  length payload ≡ Bin.size b
successorPayloadLength b payload starts =
  NatP.suc-injective
    (trans
      (sym (cong length starts))
      (Enc.successorBitsLength b))

successorPayloadNumeric :
  (b : Bin.ℕᵇ) (payload : Word.BitWord) →
  Enc.successorBits b ≡ true ∷ payload →
  Dec.pow2 (length payload) + Dec.payloadValue payload
    ≡ suc (Bin.toℕ b)
successorPayloadNumeric b payload starts =
  trans
    (cong (λ value → value + Dec.payloadValue payload)
      (sym (NatP.*-identityˡ (Dec.pow2 (length payload)))))
    (trans
      (sym (cong Dec.payloadValue starts))
      (Val.successorBitsNumericValue b))

-- This theorem does not depend on the implementation of fromℕ.
-- It works directly over any already-existing binary numeral b.
gammaBinaryNumeralReadSuffix :
  (b : Bin.ℕᵇ) (suffix : Word.BitWord) →
  Dec.readGamma
    (Enc.zeroPrefix (Bin.size b)
      ++ (Enc.successorBits b ++ suffix))
    ≡ just (Bin.toℕ b , suffix)
gammaBinaryNumeralReadSuffix b suffix
  with Enc.successorBitsLeadingOne b
... | payload , starts
  rewrite zeroPrefixSameObject (Bin.size b)
        | sym (successorPayloadLength b payload starts)
        | starts
        | Dec.readGammaPayloadExact payload suffix
        | cong (λ v → v ∸ suc zero)
            (successorPayloadNumeric b payload starts) =
  refl

-- The standard library proves toℕ (fromℕ n) = n. This joins
-- the binary numeral bridge to the ACTUAL original Nat encoder.
gammaReadEncodeSuffix :
  (n : Nat) (suffix : Word.BitWord) →
  Dec.readGamma (Enc.encodeGammaNat n ++ suffix)
    ≡ just (n , suffix)
gammaReadEncodeSuffix n suffix
  rewrite Enc.gammaPrefixExactlyBinarySize n
        | ListP.++-assoc
            (Enc.zeroPrefix (Bin.size (Bin.fromℕ n)))
            (Enc.successorBits (Bin.fromℕ n))
            suffix
        | gammaBinaryNumeralReadSuffix (Bin.fromℕ n) suffix
        | BinP.toℕ-fromℕ n =
  refl

gammaReadEncodeRoundTrip :
  (n : Nat) →
  Dec.readGamma (Enc.encodeGammaNat n)
    ≡ just (n , [])
gammaReadEncodeRoundTrip n
  rewrite sym (ListP.++-identityʳ (Enc.encodeGammaNat n)) =
  gammaReadEncodeSuffix n []
