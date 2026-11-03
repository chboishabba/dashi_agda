module DASHI.Mathematics.Complexity.Karp21GammaWeightedEdgeListRoundTripExact where

------------------------------------------------------------------------
-- E20 / N21: EXACT LITERAL EDGE-TRIPLE AND EDGE-LIST ROUNDTRIP.
--
-- For the ORIGINAL WeightedCutGraph edge type, its existing gamma
-- serializer and existing graph-word RAW parser agree on:
--    Fin vertex endpoints, signed weights, edge multiplicity/order,
--    and every unconsumed Boolean suffix.
--
-- No new graph language, dummy validity flag, unsound edge sorting,
-- or proof-field equality is introduced. Strict global canonical
-- pair-order validation and conversion back to Fin n remain distinct.
--
-- This is an integration module: the weighted graph owners have not
-- passed the Golden --safe import closure or Agda kernel acceptance.
-- Original: Karp (1972); Elias gamma; prior DASHI E20/N21 codecs.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.List.Base using (List; []; _∷_; _++_; length)
import Data.List.Properties as ListP
open import Data.Maybe.Base using (just)
import Data.Fin.Base as Fin

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21GammaBinaryGoldenCoreExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaBinaryRoundTripExact as Numeric
import DASHI.Mathematics.Complexity.Karp21GammaSignedListRoundTripExact as Signed
import DASHI.Mathematics.Complexity.Karp21GammaZigzagWordEncodeExact as Encode
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Decode

------------------------------------------------------------------------
-- A raw tuple records the exact natural-number vertex addresses,
-- signed edge weight and original list order. We intentionally do
-- NOT assert a dependent WeightedCutGraph equality, since the parser
-- must separately reconstruct Fin n and offDiagonal proof fields.
------------------------------------------------------------------------

rawOfEdge :
  ∀ {n} → Cut.SignedUndirectedEdge n → Decode.RawEdge
rawOfEdge edge =
  Decode.raw-edge
    (Fin.toℕ (Cut.first edge))
    (Fin.toℕ (Cut.second edge))
    (Cut.weight edge)

rawOfEdges :
  ∀ {n} → List (Cut.SignedUndirectedEdge n) → List Decode.RawEdge
rawOfEdges [] = []
rawOfEdges (edge ∷ rest) = rawOfEdge edge ∷ rawOfEdges rest

------------------------------------------------------------------------
-- Exact raw projection coordinates and count: the decoder's raw edge
-- carrier is not merely equinumerous, but records the same Fin-to-Nat
-- endpoints and the SAME signed weight, including negative and zero.
------------------------------------------------------------------------

rawOfEdgeFirstSame :
  ∀ {n} (edge : Cut.SignedUndirectedEdge n) →
  Decode.source (rawOfEdge edge) ≡ Fin.toℕ (Cut.first edge)
rawOfEdgeFirstSame edge = refl

rawOfEdgeSecondSame :
  ∀ {n} (edge : Cut.SignedUndirectedEdge n) →
  Decode.target (rawOfEdge edge) ≡ Fin.toℕ (Cut.second edge)
rawOfEdgeSecondSame edge = refl

rawOfEdgeSignedWeightSame :
  ∀ {n} (edge : Cut.SignedUndirectedEdge n) →
  Decode.signedWeight (rawOfEdge edge) ≡ Cut.weight edge
rawOfEdgeSignedWeightSame edge = refl

rawOfEdgesLength :
  ∀ {n} (edges : List (Cut.SignedUndirectedEdge n)) →
  length (rawOfEdges edges) ≡ length edges
rawOfEdgesLength [] = refl
rawOfEdgesLength (edge ∷ rest) =
  cong suc (rawOfEdgesLength rest)

------------------------------------------------------------------------
-- The ORIGINAL encodeEdgeWord is
-- gamma(u) ++ gamma(v) ++ gamma(zigzag(w)).
-- Reuse the SAME numeric and signed parser roundtrip proof owners.
------------------------------------------------------------------------

readActualEdgeWordSuffix :
  ∀ {n} (edge : Cut.SignedUndirectedEdge n)
    (suffix : Word.BitWord) →
  Decode.readOneRawEdge (Encode.encodeEdgeWord edge ++ suffix)
    ≡ just (rawOfEdge edge , suffix)
readActualEdgeWordSuffix edge suffix
  rewrite ListP.++-assoc
    (Gamma.encodeGammaNat (Fin.toℕ (Cut.first edge)))
    (Gamma.encodeGammaNat (Fin.toℕ (Cut.second edge))
      ++ Encode.encodeSignedGamma (Cut.weight edge))
    suffix
        | ListP.++-assoc
    (Gamma.encodeGammaNat (Fin.toℕ (Cut.second edge)))
    (Encode.encodeSignedGamma (Cut.weight edge))
    suffix
        | Numeric.gammaReadEncodeSuffix
    (Fin.toℕ (Cut.first edge))
    (Gamma.encodeGammaNat (Fin.toℕ (Cut.second edge))
      ++ (Encode.encodeSignedGamma (Cut.weight edge) ++ suffix))
        | Numeric.gammaReadEncodeSuffix
    (Fin.toℕ (Cut.second edge))
    (Encode.encodeSignedGamma (Cut.weight edge) ++ suffix)
        | Signed.readSignedGammaEncodeSuffix
    (Cut.weight edge) suffix =
  refl

------------------------------------------------------------------------
-- Complete edge-list decoding is induction on ACTUAL edge occurrences.
-- No assumption of no duplicates or globally sorted order is made:
-- this is strictly the source wire/raw parser correspondence. The
-- validator's ordering gate is a later theorem restricted to the
-- canonical E20 upper-triangle graph image.
------------------------------------------------------------------------

readActualEdgeListWordSuffix :
  ∀ {n} (edges : List (Cut.SignedUndirectedEdge n))
    (suffix : Word.BitWord) →
  Decode.readRawEdges (length edges)
    (Encode.encodeEdgeWords edges ++ suffix)
    ≡ just (rawOfEdges edges , suffix)
readActualEdgeListWordSuffix [] suffix = refl
readActualEdgeListWordSuffix (edge ∷ rest) suffix
  rewrite ListP.++-assoc
    (Encode.encodeEdgeWord edge)
    (Encode.encodeEdgeWords rest)
    suffix
        | readActualEdgeWordSuffix edge
    (Encode.encodeEdgeWords rest ++ suffix)
        | readActualEdgeListWordSuffix rest suffix =
  refl
