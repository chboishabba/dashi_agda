{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21GammaZigzagWordEncodeExact where

------------------------------------------------------------------------
-- CANONICAL WIRE ENCODING FOR KARP'S SIGNED PARTITION / MAX CUT.
--
-- This uses the STANDARD-LIBRARY BINARY NUMERAL owner to avoid
-- constructing binary digits by n unary increments. Digits are
-- derived structurally from binary n, and represent n+1 in MSB order.
--
-- gamma(n) = (bitLength(n+1)-1 zeros) ++ binary(n+1).
-- signedGamma(z) = gamma(zigzag(z)); signed zigzag is the actual
-- source-owned decoder's already proved injective integer embedding.
--
-- The source and target layouts agree by definition with
-- scripts/karp21_signed_cut_binary_codec.py; an independent Agda
-- parser/encoder roundtrip and literal standard-machine cost proof
-- remain separate obligations. Graph output is faithful only for
-- canonically ordered graph families; arbitrary WeightedCutGraph
-- edge lists can have duplicates and are NOT a canonical wire language.
--
-- Historical attribution: Karp (1972); DASHI E20/N21 codec.
-- Binary numeral conversion: Agda standard-library Data.Nat.Binary.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_∸_)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Integer.Base using (ℤ; ∣_∣)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
import Data.List.Properties as ListP
import Data.Nat.Properties as NatP
open import Relation.Binary.PropositionalEquality using (cong)
import Data.Fin.Base as Fin
import Data.Nat.Binary.Base as Bin
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Decode
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SparseGraphWordNPBoundaryExact as Graph

------------------------------------------------------------------------
-- For a binary value n, the exact MSB digits of n+1.
-- The even constructor is 2*(1+n), so n+1 appends 1 to
-- the binary digits of (n_inner+1); the odd constructor appends 0.
-- Structural recursion is on the library binary numeral tree.
------------------------------------------------------------------------

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
  rewrite ListP.length-++ (successorBits b) (true ∷ [])
        | NatP.+-comm (length (successorBits b)) (suc zero)
        | successorBitsLength b = refl
successorBitsLength (Bin.1+[2 b ])
  rewrite ListP.length-++ (successorBits b) (false ∷ [])
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

encodeSignedGamma : ℤ → Word.BitWord
encodeSignedGamma z = encodeGammaNat (Decode.zigzag z)

encodeSignedValues : List ℤ → Word.BitWord
encodeSignedValues [] = []
encodeSignedValues (z ∷ rest) =
  encodeSignedGamma z ++ encodeSignedValues rest

encodePartitionWord : List ℤ → Word.BitWord
encodePartitionWord values =
  encodeGammaNat (length values) ++ encodeSignedValues values

------------------------------------------------------------------------
-- The actual dependent Karp weighted graph carrier. A graph's edge
-- list is output in its original order; do not sort or silently merge
-- edges because that could change its signed cut objective.
------------------------------------------------------------------------

encodeEdgeWord :
  ∀ {n} → Cut.SignedUndirectedEdge n → Word.BitWord
encodeEdgeWord edge =
  encodeGammaNat (Fin.toℕ (Cut.first edge)) ++
  encodeGammaNat (Fin.toℕ (Cut.second edge)) ++
  encodeSignedGamma (Cut.weight edge)

encodeEdgeWords :
  ∀ {n} → List (Cut.SignedUndirectedEdge n) → Word.BitWord
encodeEdgeWords [] = []
encodeEdgeWords (edge ∷ rest) =
  encodeEdgeWord edge ++ encodeEdgeWords rest

encodeGraphWord : Graph.GraphInstance → Word.BitWord
encodeGraphWord (n , graph) =
  encodeGammaNat n ++
  encodeGammaNat (length (Cut.edges graph)) ++
  encodeEdgeWords (Cut.edges graph) ++
  encodeGammaNat (∣ Cut.threshold graph ∣)

------------------------------------------------------------------------
-- Small exact executable fixtures. The fixed 2-vertex +1-edge
-- graph has n=2, m=1, u=0, v=1, w=+1, W=+1, hence
-- gamma(2),gamma(1),gamma(0),gamma(1),gamma(2),gamma(1).
------------------------------------------------------------------------

gammaZeroEncoding :
  encodeGammaNat zero ≡ true ∷ []
gammaZeroEncoding = refl

gammaOneEncoding :
  encodeGammaNat (suc zero) ≡
    false ∷ true ∷ false ∷ []
gammaOneEncoding = refl

gammaTwoEncoding :
  encodeGammaNat (suc (suc zero)) ≡
    false ∷ true ∷ true ∷ []
gammaTwoEncoding = refl

emptyPartitionEncoding :
  encodePartitionWord [] ≡ true ∷ []
emptyPartitionEncoding = refl
