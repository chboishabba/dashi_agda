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
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import Data.Fin.Base as Fin
import Data.Fin.Properties as FinP
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


-- A one-bit extra suffix must be rejected at every graph size, even
-- n=0 and m=0. The certificate decoder never silently truncates.
sparseRejectTrailingBit :
  ∀ {n} {edges : List (Cut.SignedUndirectedEdge n)}
    (local : EdgeBits edges) (extra : Bool) →
  decodeSparseEdgeBits edges
    (encodeSparseEdgeBits local ++ (extra ∷ [])) ≡ nothing
sparseRejectTrailingBit emptyEdgeBits extra = refl
sparseRejectTrailingBit (addEdgeBits a b tail) extra
  rewrite sparseRejectTrailingBit tail extra = refl

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


------------------------------------------------------------------------
-- Executable Boolean correspondence and mathematical completeness
-- for a projected witness. The remaining arbitrary-certificate
-- SOUNDNESS needs the same-ID endpoint consistency construction.
------------------------------------------------------------------------

verifySparseEdgeBits :
  ∀ {n} (graph : Cut.WeightedCutGraph n) →
  EdgeBits (Cut.edges graph) → Bool
verifySparseEdgeBits graph local =
  Int._≤ᵇ_ (Cut.threshold graph)
    (sparseEdgeScore (Cut.edges graph) local)

projectedSparseVerifierExactlyEqualsFull :
  ∀ {n} (graph : Cut.WeightedCutGraph n)
    (labels : Vec.Vec Bool n) →
  verifySparseEdgeBits graph (projectEdgeBits (Cut.edges graph) labels)
    ≡ Cut.verifyWeightedMaxCut graph labels
projectedSparseVerifierExactlyEqualsFull graph labels =
  cong (Int._≤ᵇ_ (Cut.threshold graph))
    (fullWitnessHasExactSparseScore graph labels)

fullAcceptedWitnessHasSparseWitness :
  ∀ {n} (graph : Cut.WeightedCutGraph n)
    (labels : Vec.Vec Bool n) →
  Cut.verifyWeightedMaxCut graph labels ≡ true →
  verifySparseEdgeBits graph (projectEdgeBits (Cut.edges graph) labels)
    ≡ true
fullAcceptedWitnessHasSparseWitness graph labels observed =
  trans
    (projectedSparseVerifierExactlyEqualsFull graph labels)
    observed


------------------------------------------------------------------------
-- Concrete endpoint-consistency checker on a SPARSE edge-label list.
-- It compares every pair of occurrences at equal Fin n addresses;
-- the arithmetic involves at most 2m addresses (not an n-sized array).
-- Fin addresses are part of the actual graph, not inferred provenance.
------------------------------------------------------------------------

endpointObservations :
  ∀ {n} (edges : List (Cut.SignedUndirectedEdge n)) →
  EdgeBits edges → List (Fin.Fin n × Bool)
endpointObservations [] emptyEdgeBits = []
endpointObservations (edge ∷ tail) (addEdgeBits a b rest) =
  (Cut.first edge , a) ∷ (Cut.second edge , b)
  ∷ endpointObservations tail rest

boolEqual : Bool → Bool → Bool
boolEqual true true = true
boolEqual false false = true
boolEqual true false = false
boolEqual false true = false

andBool : Bool → Bool → Bool
andBool true x = x
andBool false x = false

observationsCompatible :
  ∀ {n} → (Fin.Fin n × Bool) → (Fin.Fin n × Bool) → Bool
observationsCompatible (vertex , label) (other , otherLabel)
  with FinP._≟_ vertex other
... | yes _ = boolEqual label otherLabel
... | no _ = true

oneAgainstAll :
  ∀ {n} →
  (Fin.Fin n × Bool) → List (Fin.Fin n × Bool) → Bool
oneAgainstAll observation [] = true
oneAgainstAll observation (other ∷ rest) =
  andBool (observationsCompatible observation other)
    (oneAgainstAll observation rest)

allEndpointOccurrencesConsistent :
  ∀ {n} → List (Fin.Fin n × Bool) → Bool
allEndpointOccurrencesConsistent [] = true
allEndpointOccurrencesConsistent (one ∷ rest) =
  andBool (oneAgainstAll one rest)
    (allEndpointOccurrencesConsistent rest)

-- Source-written executable verifier aligned with the Python sparse
-- certificate semantics (same-edge double-bit representation, same
-- endpoint consistency condition and same signed threshold).
verifyConsistentSparseCut :
  ∀ {n} (graph : Cut.WeightedCutGraph n) →
  EdgeBits (Cut.edges graph) → Bool
verifyConsistentSparseCut graph local =
  andBool
    (allEndpointOccurrencesConsistent
      (endpointObservations (Cut.edges graph) local))
    (verifySparseEdgeBits graph local)

verifySparseCutBitWord :
  ∀ {n} (graph : Cut.WeightedCutGraph n) →
  List Bool → Bool
verifySparseCutBitWord graph bits
  with decodeSparseEdgeBits (Cut.edges graph) bits
... | nothing = false
... | just local = verifyConsistentSparseCut graph local

-- This real verifier REJECTS a malformed one-bit suffix, not a
-- success flag. It applies even when no edges are listed.
sparseWordVerifierRejectsTrailingBit :
  ∀ {n} (graph : Cut.WeightedCutGraph n)
    (local : EdgeBits (Cut.edges graph)) (extra : Bool) →
  verifySparseCutBitWord graph
    (encodeSparseEdgeBits local ++ (extra ∷ [])) ≡ false
sparseWordVerifierRejectsTrailingBit graph local extra
  rewrite sparseRejectTrailingBit local extra = refl


------------------------------------------------------------------------
-- SPARSE VERIFIER COMPLETENESS on actual projected full assignments.
-- Every edge endpoint in the projection reads the SAME original vertex
-- lookup; repeated occurrences therefore satisfy the real checker.
------------------------------------------------------------------------

vertexOccurrences :
  ∀ {n} → List (Cut.SignedUndirectedEdge n) → List (Fin.Fin n)
vertexOccurrences [] = []
vertexOccurrences (edge ∷ tail) =
  Cut.first edge ∷ Cut.second edge ∷ vertexOccurrences tail

observationsOfVertices :
  ∀ {n} → List (Fin.Fin n) → Vec.Vec Bool n →
  List (Fin.Fin n × Bool)
observationsOfVertices [] labels = []
observationsOfVertices (v ∷ rest) labels =
  (v , Vec.lookup labels v) ∷ observationsOfVertices rest labels

projectedObservationsAreActualVertexLookups :
  ∀ {n} (edges : List (Cut.SignedUndirectedEdge n))
    (labels : Vec.Vec Bool n) →
  endpointObservations edges (projectEdgeBits edges labels)
  ≡ observationsOfVertices (vertexOccurrences edges) labels
projectedObservationsAreActualVertexLookups [] labels = refl
projectedObservationsAreActualVertexLookups (edge ∷ tail) labels =
  cong (λ rest →
      (Cut.first edge , Vec.lookup labels (Cut.first edge))
      ∷ (Cut.second edge , Vec.lookup labels (Cut.second edge))
      ∷ rest)
    (projectedObservationsAreActualVertexLookups tail labels)

boolEqualSelf :
  (value : Bool) → boolEqual value value ≡ true
boolEqualSelf true = refl
boolEqualSelf false = refl

equalVertexObservationsAlwaysCompatible :
  ∀ {n} (labels : Vec.Vec Bool n) (v w : Fin.Fin n) →
  observationsCompatible
    (v , Vec.lookup labels v)
    (w , Vec.lookup labels w) ≡ true
equalVertexObservationsAlwaysCompatible labels v w
  with FinP._≟_ v w
... | yes refl = boolEqualSelf (Vec.lookup labels v)
... | no _ = refl

oneVersusActualVertexObservations :
  ∀ {n} (labels : Vec.Vec Bool n) (v : Fin.Fin n)
    (vertices : List (Fin.Fin n)) →
  oneAgainstAll
    (v , Vec.lookup labels v)
    (observationsOfVertices vertices labels)
  ≡ true
oneVersusActualVertexObservations labels v [] = refl
oneVersusActualVertexObservations labels v (w ∷ tail)
  rewrite equalVertexObservationsAlwaysCompatible labels v w
        | oneVersusActualVertexObservations labels v tail =
  refl

allActualVertexObservationsConsistent :
  ∀ {n} (labels : Vec.Vec Bool n)
    (vertices : List (Fin.Fin n)) →
  allEndpointOccurrencesConsistent
    (observationsOfVertices vertices labels) ≡ true
allActualVertexObservationsConsistent labels [] = refl
allActualVertexObservationsConsistent labels (v ∷ tail)
  rewrite oneVersusActualVertexObservations labels v tail
        | allActualVertexObservationsConsistent labels tail = refl

projectedSparseCertificateAlwaysConsistent :
  ∀ {n} (edges : List (Cut.SignedUndirectedEdge n))
    (labels : Vec.Vec Bool n) →
  allEndpointOccurrencesConsistent
    (endpointObservations edges (projectEdgeBits edges labels)) ≡ true
projectedSparseCertificateAlwaysConsistent edges labels
  rewrite projectedObservationsAreActualVertexLookups edges labels =
  allActualVertexObservationsConsistent labels
    (vertexOccurrences edges)

-- Exact acceptance equality for the actual sparsity/consistency
-- verifier, not merely its unconstrained signed objective.
projectedConsistentSparseVerifierEqualsOriginal :
  ∀ {n} (graph : Cut.WeightedCutGraph n)
    (labels : Vec.Vec Bool n) →
  verifyConsistentSparseCut graph
    (projectEdgeBits (Cut.edges graph) labels)
  ≡ Cut.verifyWeightedMaxCut graph labels
projectedConsistentSparseVerifierEqualsOriginal graph labels
  rewrite projectedSparseCertificateAlwaysConsistent
    (Cut.edges graph) labels =
  projectedSparseVerifierExactlyEqualsFull graph labels

projectedSparseBitWordVerifierEqualsOriginal :
  ∀ {n} (graph : Cut.WeightedCutGraph n)
    (labels : Vec.Vec Bool n) →
  verifySparseCutBitWord graph
    (encodeSparseEdgeBits (projectEdgeBits (Cut.edges graph) labels))
  ≡ Cut.verifyWeightedMaxCut graph labels
projectedSparseBitWordVerifierEqualsOriginal graph labels
  rewrite sparseDecodeEncode
    (projectEdgeBits (Cut.edges graph) labels) =
  projectedConsistentSparseVerifierEqualsOriginal graph labels
