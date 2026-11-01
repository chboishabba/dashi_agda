module DASHI.Crypto.SearchGraphEmbeddingDistortionExact where

------------------------------------------------------------------------
-- EDGE-WEIGHTED SEARCH-GRAPH EMBEDDING DISTORTION
--
-- The candidate/search carrier supplies vertices and transition edges; an
-- implementation supplies a code and code-space distance.  Distortion is
-- accumulated along actual search edges rather than inferred from storage rate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

record TransitionEdge (State : Set) : Set where
  constructor transitionEdge
  field
    from to : State
    weight : Nat

open TransitionEdge public

record SearchGraph : Set₁ where
  constructor searchGraph
  field
    State : Set
    edges : List (TransitionEdge State)

open SearchGraph public

record CodeEmbedding (graph : SearchGraph) : Set₁ where
  constructor codeEmbedding
  field
    Code : Set
    encode : State graph → Code
    distance : Code → Code → Nat

open CodeEmbedding public

edgeEmbeddingCost :
  ∀ {graph : SearchGraph} →
  CodeEmbedding graph → TransitionEdge (State graph) → Nat
edgeEmbeddingCost embedding edge =
  weight edge *
  distance embedding (encode embedding (from edge)) (encode embedding (to edge))

embeddingDistortion :
  ∀ {graph : SearchGraph} → CodeEmbedding graph → Nat
embeddingDistortion {graph} embedding = fold (edges graph)
  where
  fold : List (TransitionEdge (State graph)) → Nat
  fold [] = 0
  fold (edge ∷ rest) = edgeEmbeddingCost embedding edge + fold rest

------------------------------------------------------------------------
-- Finite P4 regression: same three graph edges, two 2-bit embeddings.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
import DASHI.Crypto.GrayPathTransitionOptimalExact as Gray

data P4 : Set where q0 q1 q2 q3 : P4

p4Graph : SearchGraph
p4Graph = searchGraph P4
  (transitionEdge q0 q1 1 ∷
   transitionEdge q1 q2 1 ∷
   transitionEdge q2 q3 1 ∷ [])

binaryCode : P4 → Gray.Bit2
binaryCode q0 = Gray.bit2 false false
binaryCode q1 = Gray.bit2 false true
binaryCode q2 = Gray.bit2 true false
binaryCode q3 = Gray.bit2 true true

grayCode : P4 → Gray.Bit2
grayCode q0 = Gray.bit2 false false
grayCode q1 = Gray.bit2 false true
grayCode q2 = Gray.bit2 true true
grayCode q3 = Gray.bit2 true false

binaryEmbedding : CodeEmbedding p4Graph
binaryEmbedding = codeEmbedding Gray.Bit2 binaryCode Gray.hamming2

grayEmbedding : CodeEmbedding p4Graph
grayEmbedding = codeEmbedding Gray.Bit2 grayCode Gray.hamming2

binaryEmbeddingDistortionIs4 : embeddingDistortion binaryEmbedding ≡ 4
binaryEmbeddingDistortionIs4 = refl

grayEmbeddingDistortionIs3 : embeddingDistortion grayEmbedding ≡ 3
grayEmbeddingDistortionIs3 = refl

sameGraphSameRateDifferentEmbeddingGeometry :
  embeddingDistortion binaryEmbedding ≡ 4
  × embeddingDistortion grayEmbedding ≡ 3
sameGraphSameRateDifferentEmbeddingGeometry = refl , refl
  where
  open import Data.Product using (_×_; _,_)
