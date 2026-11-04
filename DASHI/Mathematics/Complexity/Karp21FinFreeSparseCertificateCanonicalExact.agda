module DASHI.Mathematics.Complexity.Karp21FinFreeSparseCertificateCanonicalExact where

------------------------------------------------------------------------
-- N21: ORIGINAL 2m-BIT SPARSE CERTIFICATE PARSER CANONICALITY AND
-- ORIGINAL FIN-FREE SCORER REJECTION ON EVERY MALFORMED BITWORD.
--
-- The already existing Sparse.sparseDecodeEncode establishes one
-- direction. This module proves the other on every successful
-- Sparse.decodeSparseEdgeBits run and shows the actual rawSparseScore
-- never accepts any certificate that the SAME typed edge-list decoder
-- rejects. No new grammar, fresh equality oracle, or n-sized witness.
--
-- The full signed-threshold Boolean verifier equality, graph-word
-- malformed cases, binary tape clock and Agda kernel receipt remain.
-- Original Karp 1972; DASHI sparse certificate / raw score owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; subst)
import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21RawGraphValidatorObservationExact as Observe

SparseDecodedCanonical :
  ∀ {n : Nat}
    (edges : List (Cut.SignedUndirectedEdge n))
    (word : List Bool) →
  Maybe (Sparse.EdgeBits edges) → Set
SparseDecodedCanonical edges word nothing = ⊤
SparseDecodedCanonical edges word (just local) =
  Sparse.encodeSparseEdgeBits local ≡ word

sparseDecodeCanonicalOutcome :
  ∀ {n : Nat}
    (edges : List (Cut.SignedUndirectedEdge n))
    (word : List Bool) →
  SparseDecodedCanonical edges word
    (Sparse.decodeSparseEdgeBits edges word)
sparseDecodeCanonicalOutcome [] [] = refl
sparseDecodeCanonicalOutcome [] (_ ∷ _) = tt
sparseDecodeCanonicalOutcome (_ ∷ _) [] = tt
sparseDecodeCanonicalOutcome (_ ∷ _) (_ ∷ []) = tt
sparseDecodeCanonicalOutcome (edge ∷ rest) (a ∷ b ∷ bits)
  with Sparse.decodeSparseEdgeBits rest bits
     | sparseDecodeCanonicalOutcome rest bits
... | nothing | _ = tt
... | just tailLocal | proof =
  cong (λ suffix → a ∷ b ∷ suffix) proof

sparseDecodedWordIsExactOriginalEncoding :
  ∀ {n : Nat}
    (edges : List (Cut.SignedUndirectedEdge n))
    (word : List Bool)
    (local : Sparse.EdgeBits edges) →
  Sparse.decodeSparseEdgeBits edges word ≡ just local →
  Sparse.encodeSparseEdgeBits local ≡ word
sparseDecodedWordIsExactOriginalEncoding edges word local accepted =
  subst (SparseDecodedCanonical edges word) accepted
    (sparseDecodeCanonicalOutcome edges word)

justNotNothing :
  ∀ {A : Set} {x : A} → just x ≡ nothing → ⊥
justNotNothing ()

-- On every word rejected by the original typed 2m decoder, the
-- ACTUAL source Runtime.rawSparseScore rejects with nothing, even
-- under an arbitrary previous endpoint history.
rawScoreCannotAcceptMalformedSparseBits :
  ∀ {n : Nat}
    (raw : List Graph.RawEdge)
    (typed : List (Cut.SignedUndirectedEdge n))
    (fields : Observe.RawEdgeListFieldsSame raw typed)
    (word : List Bool)
    (history : List (Nat × Bool)) →
  Sparse.decodeSparseEdgeBits typed word ≡ nothing →
  Runtime.rawSparseScore raw word history ≡ nothing
rawScoreCannotAcceptMalformedSparseBits [] []
  Observe.raw-list-nil [] history ()
rawScoreCannotAcceptMalformedSparseBits [] []
  Observe.raw-list-nil (_ ∷ _) history rejected = refl
rawScoreCannotAcceptMalformedSparseBits
  (r ∷ rs) (edge ∷ es)
  (Observe.raw-list-cons fields tailFields)
  [] history rejected = refl
rawScoreCannotAcceptMalformedSparseBits
  (r ∷ rs) (edge ∷ es)
  (Observe.raw-list-cons fields tailFields)
  (a ∷ []) history rejected = refl
rawScoreCannotAcceptMalformedSparseBits
  (r ∷ rs) (edge ∷ es)
  (Observe.raw-list-cons fields tailFields)
  (a ∷ b ∷ bits) history rejected
  with Sparse.decodeSparseEdgeBits es bits
... | just tailLocal =
  ⊥-elim (justNotNothing rejected)
... | nothing
  with Runtime.endpointConsistent (Graph.source r) a history
     | Runtime.endpointConsistent (Graph.target r) b history
...   | false | _ = refl
...   | true | false = refl
...   | true | true
  rewrite rawScoreCannotAcceptMalformedSparseBits
    rs es tailFields bits
    ((Graph.source r , a) ∷ (Graph.target r , b) ∷ history)
    refl = refl
