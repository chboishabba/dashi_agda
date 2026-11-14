module DASHI.Mathematics.Complexity.Karp21GammaZigzagWordEncodeExact where

-- Integration owner: not --safe until the imported weighted-graph
-- theorem chain is independently checked and transitively --safe.

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
import Data.Maybe.Base
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact as Golden
import DASHI.Mathematics.Complexity.Karp21GammaSignedListRoundTripExact as Pure
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Decode
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SparseGraphWordNPBoundaryExact as Graph

------------------------------------------------------------------------
-- For a binary value n, the exact MSB digits of n+1.
-- The even constructor is 2*(1+n), so n+1 appends 1 to
-- the binary digits of (n_inner+1); the odd constructor appends 0.
-- Structural recursion is on the library binary numeral tree.
------------------------------------------------------------------------

open Golden public using
  ( successorBits
  ; successorBitsLeadingOne
  ; successorBitsLength
  ; zeroPrefix
  ; encodeGammaNat
  ; gammaPrefixExactlyBinarySize
  )

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
-- ORIGINAL E20 SOURCE ENCODER = PURE GOLDEN SIGNED LIST ENCODER.
-- The recursive equality is explicit: gamma and zigzag are
-- source-owned single functions, not a pair of proxy representations.
------------------------------------------------------------------------

encodedSignedValuesSamePure :
  (values : List ℤ) →
  encodeSignedValues values ≡ Pure.encodeSignedValuesPure values
encodedSignedValuesSamePure [] = refl
encodedSignedValuesSamePure (value ∷ rest) =
  cong (λ suffix → encodeSignedGamma value ++ suffix)
    (encodedSignedValuesSamePure rest)

encodedPartitionWordSamePure :
  (values : List ℤ) →
  encodePartitionWord values ≡ Pure.encodePartitionWordPure values
encodedPartitionWordSamePure values =
  cong
    (λ bits → encodeGammaNat (length values) ++ bits)
    (encodedSignedValuesSamePure values)

-- Actual graph/E20 input serialization, ACTUAL same-word parser.
partitionWordDecodeEncode :
  (values : List ℤ) →
  Decode.decodePartitionWord (encodePartitionWord values)
    ≡ Data.Maybe.Base.just values
partitionWordDecodeEncode values
  rewrite encodedPartitionWordSamePure values =
  Pure.partitionWordDecodeEncode values

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
