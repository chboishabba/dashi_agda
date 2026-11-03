module DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact where

------------------------------------------------------------------------
-- N21: SOURCE-WRITTEN FIN-FREE SPARSE GRAPH WORD VERIFIER.
--
-- The original typed graph parser constructs Fin n values from
-- binary gamma endpoint addresses. Such explicit constructors can
-- have exponentially more nodes than the endpoint's input word.
--
-- This alternate *runtime path* consumes the SAME original gamma
-- signed graph word and the SAME exactly-two-bits-per-edge witness.
-- It reuses the original readGamma, readRawEdges, strictAfter, signed
-- integer arithmetic and Boolean comparison owners. It constructs NO
-- Fin n endpoint, Vec Bool n or n-indexed array. It checks original
-- per-edge u<v<n and canonical strict pair order in raw form, then
-- pairwise consistency of all endpoint occurrences and signed score.
--
-- A subsequent observational same-word theorem must prove equality
-- with the existing typed Cut.WeightedMaxCutYES / N21 verifier.
-- No polynomialTimeVerifier witness is asserted without machine
-- clock evidence; Agda kernel acceptance remains pending.
--
-- Attribution: Richard Karp (1972); DASHI original signed gamma
-- graph-word and sparse 2m endpoint-certificate proof owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Integer.Base as Int using (ℤ; +_; _+_)
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BoolGoldenExact as Boolean
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Gamma
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph

------------------------------------------------------------------------
-- Literal raw-graph input representation. This is just a runtime
-- AST for the ORIGINAL gamma syntax, not a new weighted cut language.
------------------------------------------------------------------------

record ParsedRawGraph : Set where
  constructor parsed-raw-graph
  field
    rawVertices : Nat
    rawEdges : List Graph.RawEdge
    positiveThreshold : Nat

open ParsedRawGraph public

-- Compare original gamma-decoded integer addresses; do NOT traverse
-- a unary Fin endpoint. Equality returns a Dec without hidden oracle.
validRawEdges : Nat → Graph.PreviousPair → List Graph.RawEdge → Bool
validRawEdges n prev [] = true
validRawEdges n prev (Graph.raw-edge u v w ∷ rest)
  with NatP._<?_ u v | NatP._<?_ v n | Graph.strictAfter prev u v
... | yes _ | yes _ | true =
  validRawEdges n (Graph.previous u v) rest
... | _ | _ | _ = false

-- Same wire header, 3m field-count guard, original raw triples,
-- nonzero gamma(W), and exact end-of-word suffix policy.
readRawGraphWord : Word.BitWord → Maybe ParsedRawGraph
readRawGraphWord word with Gamma.readGamma word
... | nothing = nothing
... | just (n , afterN) with Gamma.readGamma afterN
...   | nothing = nothing
...   | just (m , afterM)
  with NatP._≤?_ (m * suc (suc (suc zero))) (length afterM)
...     | no _ = nothing
...     | yes _ with Graph.readRawEdges m afterM
...       | nothing = nothing
...       | just (edges , afterEdges) with Gamma.readGamma afterEdges
...         | nothing = nothing
...         | just (zero , _) = nothing
...         | just (suc threshold , []) with
            validRawEdges n Graph.noPrevious edges
...           | true =
  just (parsed-raw-graph n edges (suc threshold))
...           | false = nothing
...         | just (suc threshold , _ ∷ _) = nothing

------------------------------------------------------------------------
-- Pairwise consistency uses exactly the original vertex addresses.
-- This is deterministic O(m²) in the NUMBER of endpoint comparisons,
-- not a heuristic constant-time hash map. The bit complexity of
-- numerical comparison still requires the selected tape model.
------------------------------------------------------------------------

endpointConsistent :
  Nat → Bool → List (Nat × Bool) → Bool
endpointConsistent vertex selected [] = true
endpointConsistent vertex selected ((other , observed) ∷ rest)
  with NatP._≟_ vertex other
... | yes _ =
  Boolean.andBool
    (Boolean.boolEqual selected observed)
    (endpointConsistent vertex selected rest)
... | no _ =
  endpointConsistent vertex selected rest

rawSparseScore :
  List Graph.RawEdge →
  Word.BitWord →
  List (Nat × Bool) →
  Maybe ℤ
rawSparseScore [] [] history = just (+ zero)
rawSparseScore [] (_ ∷ _) history = nothing
rawSparseScore (_ ∷ _) [] history = nothing
rawSparseScore (_ ∷ _) (_ ∷ []) history = nothing
rawSparseScore (Graph.raw-edge u v w ∷ edges) (a ∷ b ∷ bits)
  history
  with endpointConsistent u a history
     | endpointConsistent v b history
... | true | true
  with rawSparseScore edges bits ((u , a) ∷ (v , b) ∷ history)
...   | nothing = nothing
...   | just remaining with Boolean.boolEqual a b
...     | true = just remaining
...     | false = just (w + remaining)
... | _ | _ = nothing

verifyFinFreeSparseGraphWord :
  Word.BitWord → Word.BitWord → Bool
verifyFinFreeSparseGraphWord word certificate
  with readRawGraphWord word
... | nothing = false
... | just graph with rawSparseScore (rawEdges graph) certificate []
...   | nothing = false
...   | just score =
  Int._≤ᵇ_ (+ (positiveThreshold graph)) score

------------------------------------------------------------------------
-- Deliberately NO PR.InNP or PR.polynomialTimeVerifier proof here.
-- The required next proof is pointwise equality on the SAME inputs:
--   verifyFinFreeSparseGraphWord word certificate
--     ≡ N21.LiteralN21.verifyCanonicalSparseGraphWord word certificate.
-- Then bind a checked bit-tape clock to the fin-free path.
------------------------------------------------------------------------
