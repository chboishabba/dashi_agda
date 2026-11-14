{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact where

------------------------------------------------------------------------
-- GOLDEN P1 binary gamma(n+1) source-only encoder.
-- Pure binary numeral owner; no weighted graph, NP, verifier, or
-- arbitrary reduction imports.  The exact proof obligations for
-- gamma decoding can now be closed against a transitive-safe core.
--
-- Attribution: Elias gamma coding; Agda standard library binary
-- numeral constructors/fromℕ; DASHI signed E20/N21 Python codec.
-- Source-written only; Agda kernel acceptance remains outstanding.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_∸_)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Product using (Σ; _,_)
import Data.List.Properties as ListP
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong)
import Data.Nat.Binary.Base as Bin
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word

successorBits : Bin.ℕᵇ → Word.BitWord
successorBits Bin.zero = true ∷ []
successorBits (Bin.2[1+ n ]) =
  successorBits n ++ (true ∷ [])
successorBits (Bin.1+[2 n ]) =
  successorBits n ++ (false ∷ [])

------------------------------------------------------------------------
-- Certified gamma header shape. These proofs use the original binary
-- numeral tree, not unary search for a leading bit.
-- For any numeral b: successorBits b begins with ONE and has exactly
-- 1 + Bin.size b bits. Hence gamma's zero-prefix length is the exact
-- remaining payload bit count for the same numeral.
------------------------------------------------------------------------

successorBitsLeadingOne :
  (b : Bin.ℕᵇ) →
  Σ Word.BitWord (λ payload → successorBits b ≡ true ∷ payload)
successorBitsLeadingOne Bin.zero = [] , refl
successorBitsLeadingOne (Bin.2[1+ b ]) with successorBitsLeadingOne b
... | payload , leading =
  (payload ++ (true ∷ [])) ,
  cong (λ digits → digits ++ (true ∷ [])) leading
successorBitsLeadingOne (Bin.1+[2 b ]) with successorBitsLeadingOne b
... | payload , leading =
  (payload ++ (false ∷ [])) ,
  cong (λ digits → digits ++ (false ∷ [])) leading

successorBitsLength :
  (b : Bin.ℕᵇ) →
  length (successorBits b) ≡ suc (Bin.size b)
successorBitsLength Bin.zero = refl
successorBitsLength (Bin.2[1+ b ])
  rewrite ListP.length-++ (successorBits b) {ys = true ∷ []}
        | NatP.+-comm (length (successorBits b)) (suc zero)
        | successorBitsLength b = refl
successorBitsLength (Bin.1+[2 b ])
  rewrite ListP.length-++ (successorBits b) {ys = false ∷ []}
        | NatP.+-comm (length (successorBits b)) (suc zero)
        | successorBitsLength b = refl

zeroPrefix : Nat → Word.BitWord
zeroPrefix zero = []
zeroPrefix (suc n) = false ∷ zeroPrefix n

encodeGammaNat : Nat → Word.BitWord
encodeGammaNat n =
  zeroPrefix (length digits ∸ suc zero) ++ digits
  where
    digits : Word.BitWord
    digits = successorBits (Bin.fromℕ n)

-- Shape lemma used by the future full numeric gamma parser inverse:
-- the encoded prefix length is exactly Bin.size(fromℕ n), not a
-- guessed bit width from the magnitude of n.
gammaPrefixExactlyBinarySize :
  (n : Nat) →
  zeroPrefix (length (successorBits (Bin.fromℕ n)) ∸ suc zero)
    ≡ zeroPrefix (Bin.size (Bin.fromℕ n))
gammaPrefixExactlyBinarySize n
  rewrite successorBitsLength (Bin.fromℕ n) = refl

