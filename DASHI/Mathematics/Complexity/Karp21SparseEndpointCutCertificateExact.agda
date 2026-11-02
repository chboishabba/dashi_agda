module DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact where

------------------------------------------------------------------------
-- N21 CRITICAL BINARY ENCODING CORRECTION:
--
-- In the canonical Python GraphWord codec, vertexCount n is BINARY.
-- A graph with m=0 and arbitrary enormous n has a tiny input length.
-- Therefore the earlier exact Vec Bool n certificate, although faithful,
-- does NOT prove a polynomial certificate bound in encoded input length.
--
-- Instead use TWO Boolean bits per actual edge occurrence. This
-- source-written module constructs the dependent length-2m edge-endpoint
-- bit certificate from ANY full vertex assignment, with:
--   * an exact length and total reject-trailing-bits binary decoder;
--   * roundtrip of every certificate on its same edge-list carrier;
--   * exact equality of signed edge-list scores for every assignment.
--
-- Soundness for arbitrary encoded SPARSE certificates requires a
-- separately checkable endpoint-CONSISTENCY test: all occurrences of
-- one Fin n vertex must carry the same Boolean value. The Python
-- reference implementation now supplies that check and a 2m-bit
-- verifier without allocating an n-vertex array.
--
-- To produce PR.InNP in Agda still prove:
-- (1) soundness of consistency implies global-cut extension;
-- (2) this finite typed graph is the same GraphWord decoder result;
-- (3) real verifier machine clock over signed bit arithmetic and
--     canonical input encoding size, including all malformed words.
--
-- Original mathematical source: Karp 1972. DASHI prior owners:
-- Karp21FiniteWeightedMaxCutVerifierExact, FiniteWordSizeExact.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import Data.Vec.Base as Vec
import Data.Integer.Base as Int
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word

-- Exactly two endpoint Boolean bits for each literal signed edge
-- occurrence, with no dependence on total number of vertex IDs.
data EdgeBits {n : Nat} :
    List (Cut.SignedUndirectedEdge n) → Set where
  emptyEdgeBits : EdgeBits []
  addEdgeBits :
    ∀ {edge tail} →
    (left right : Bool) →
    EdgeBits tail →
    EdgeBits (edge ∷ tail)

encodeSparseEdgeBits :
  ∀ {n} {edges : List (Cut.SignedUndirectedEdge n)} →
  EdgeBits edges → List Bool
encodeSparseEdgeBits emptyEdgeBits = []
encodeSparseEdgeBits (addEdgeBits a b tail) =
  a ∷ b ∷ encodeSparseEdgeBits tail

decodeSparseEdgeBits :
  ∀ {n} (edges : List (Cut.SignedUndirectedEdge n)) →
  List Bool → Maybe (EdgeBits edges)
decodeSparseEdgeBits [] [] = just emptyEdgeBits
decodeSparseEdgeBits [] (_ ∷ _) = nothing
decodeSparseEdgeBits (_ ∷ _) [] = nothing
decodeSparseEdgeBits (_ ∷ _) (_ ∷ []) = nothing
decodeSparseEdgeBits (edge ∷ tail) (a ∷ b ∷ rest)
  with decodeSparseEdgeBits tail rest
... | nothing = nothing
... | just proof = just (addEdgeBits a b proof)

sparseDecodeEncode :
  ∀ {n} {edges : List (Cut.SignedUndirectedEdge n)}
    (local : EdgeBits edges) →
  decodeSparseEdgeBits edges (encodeSparseEdgeBits local)
  ≡ just local
sparseDecodeEncode emptyEdgeBits = refl
sparseDecodeEncode (addEdgeBits a b tail)
  rewrite sparseDecodeEncode tail = refl

-- Correct 2m witness size, defined by a linear recurrence so no
-- arithmetic import/associativity assumptions are hidden in a code.
twoPerEdge : Nat → Nat
twoPerEdge zero = zero
twoPerEdge (suc m) = suc (suc (twoPerEdge m))

sparseWordBitCount :
  ∀ {n} {edges : List (Cut.SignedUndirectedEdge n)}
    (local : EdgeBits edges) →
  Word.encodingSize (encodeSparseEdgeBits local)
    ≡ twoPerEdge (length edges)
sparseWordBitCount emptyEdgeBits = refl
sparseWordBitCount (addEdgeBits a b tail) =
  cong (λ m → suc (suc m))
    (sparseWordBitCount tail)

-- The real projection from a full Vec Bool n to edge-endpoint bits.
-- This is used to prove completeness, not as the new NP witness.
projectEdgeBits :
  ∀ {n} (edges : List (Cut.SignedUndirectedEdge n)) →
  Vec.Vec Bool n → EdgeBits edges
projectEdgeBits [] labels = emptyEdgeBits
projectEdgeBits (edge ∷ tail) labels =
  addEdgeBits
    (Vec.lookup labels (Cut.first edge))
    (Vec.lookup labels (Cut.second edge))
    (projectEdgeBits tail labels)

edgeBitsCut :
  Int.ℤ → Bool → Bool → Int.ℤ
edgeBitsCut weight first second
  with Cut.differentLabels first second
... | true = weight
... | false = Int.+ 0

sparseEdgeScore :
  ∀ {n} (edges : List (Cut.SignedUndirectedEdge n)) →
  EdgeBits edges → Int.ℤ
sparseEdgeScore [] emptyEdgeBits = Int.+ 0
sparseEdgeScore (edge ∷ tail) (addEdgeBits a b rest) =
  Int._+_ (edgeBitsCut (Cut.weight edge) a b)
    (sparseEdgeScore tail rest)

-- Unfold both independently owned with-patterns on the same actual
-- Boolean endpoint comparison; do not assume their names are equal.
edgeBitsCutMatchesContribution :
  ∀ {n} (edge : Cut.SignedUndirectedEdge n)
    (labels : Vec.Vec Bool n) →
  edgeBitsCut (Cut.weight edge)
    (Vec.lookup labels (Cut.first edge))
    (Vec.lookup labels (Cut.second edge))
  ≡ Cut.edgeContribution edge labels
edgeBitsCutMatchesContribution edge labels
  with Cut.differentLabels
    (Vec.lookup labels (Cut.first edge))
    (Vec.lookup labels (Cut.second edge))
... | true = refl
... | false = refl

-- This is exactly the original signed MaxCut edge objective (not a
-- PSD approximation or a nonnegative-only graph).
projectedEdgeScoreEqualsOriginal :
  ∀ {n} (edges : List (Cut.SignedUndirectedEdge n))
    (labels : Vec.Vec Bool n) →
  sparseEdgeScore edges (projectEdgeBits edges labels)
  ≡ Cut.edgeListCutValue edges labels
projectedEdgeScoreEqualsOriginal [] labels = refl
projectedEdgeScoreEqualsOriginal (edge ∷ tail) labels =
  cong₂ Int._+_
    (edgeBitsCutMatchesContribution edge labels)
    (projectedEdgeScoreEqualsOriginal tail labels)

-- Every full graph certificate projects to a *short* edge-local code
-- with the very same score, including negative weights and repeats.
fullWitnessHasExactSparseScore :
  ∀ {n} (graph : Cut.WeightedCutGraph n)
    (labels : Vec.Vec Bool n) →
  sparseEdgeScore (Cut.edges graph)
    (projectEdgeBits (Cut.edges graph) labels)
    ≡ Cut.cutValue graph labels
fullWitnessHasExactSparseScore graph labels =
  projectedEdgeScoreEqualsOriginal (Cut.edges graph) labels

fullWitnessHasTwoBitsPerListedEdge :
  ∀ {n} (graph : Cut.WeightedCutGraph n)
    (labels : Vec.Vec Bool n) →
  Word.encodingSize
    (encodeSparseEdgeBits
      (projectEdgeBits (Cut.edges graph) labels))
    ≡ twoPerEdge (length (Cut.edges graph))
fullWitnessHasTwoBitsPerListedEdge graph labels =
  sparseWordBitCount (projectEdgeBits (Cut.edges graph) labels)
