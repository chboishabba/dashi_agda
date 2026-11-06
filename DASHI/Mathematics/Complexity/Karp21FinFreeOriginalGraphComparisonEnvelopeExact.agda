module DASHI.Mathematics.Complexity.Karp21FinFreeOriginalGraphComparisonEnvelopeExact where

------------------------------------------------------------------------
-- K05 ORIGINAL successful N21 graph word:
-- BOTH raw validator comparison count AND endpoint-consistency scans.
--
-- This closes the source-owned composition:
--   raw validator: at most 3m comparisons on original raw edges;
--   endpoint history: exactly 2m(m-1) potential comparisons;
--   original successful gamma input-word: 2m <= |word|.
--
-- Thus the whole selected pair/endpoint COMPARISON COUNT is bounded
-- by the explicit quadratic expression C(L) + 3L for input bit length
-- L. Binary arithmetic and parsing work are NOT included.
-- No cost oracle, alternative graph decoder or synthetic language.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (length)
open import Data.Nat.Base using (_≤_)
open import Data.Maybe.Base using (just)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21FinFreeRawValidatorComparisonCountExact as Validate
import DASHI.Mathematics.Complexity.Karp21FinFreeOriginalWordComparisonBoundExact as History

comparisonCountForParsedGraph : Runtime.ParsedRawGraph → Nat
comparisonCountForParsedGraph graph =
  History.comparisonPolynomial (length (Runtime.rawEdges graph))
  + 3 * length (Runtime.rawEdges graph)

actualValidatedComparisonCount : Runtime.ParsedRawGraph → Nat
actualValidatedComparisonCount graph =
  History.comparisonPolynomial (length (Runtime.rawEdges graph))
  + Data.Product.proj₂
      (Validate.countedRawValidator
        (Runtime.rawVertices graph)
        Graph.noPrevious
        (Runtime.rawEdges graph))

import Data.Product

-- First account for the original validator's exact observed count,
-- not a presumed constant-time check per edge.
actualComparisonCountBelowSchedule :
  (graph : Runtime.ParsedRawGraph) →
  actualValidatedComparisonCount graph ≤ comparisonCountForParsedGraph graph
actualComparisonCountBelowSchedule graph =
  NatP.+-mono-≤
    NatP.≤-refl
    (Validate.originalRawValidatorComparisonCountBound
      (Runtime.rawVertices graph)
      Graph.noPrevious
      (Runtime.rawEdges graph))

-- The actual original gamma word supplies m <= |word| from its 3m
-- header guard and the source-owned literal raw-edge parser proof.
successfulOriginalGraphCombinedComparisonBound :
  (word : Word.BitWord)
  (graph : Runtime.ParsedRawGraph) →
  Runtime.readRawGraphWord word ≡ just graph →
  actualValidatedComparisonCount graph
    ≤ History.comparisonPolynomial (Word.encodingSize word)
      + 3 * Word.encodingSize word
successfulOriginalGraphCombinedComparisonBound word graph parsed =
  NatP.≤-trans
    (actualComparisonCountBelowSchedule graph)
    (NatP.+-mono-≤
      (History.successfulWordComparisonBound word graph parsed)
      (NatP.*-mono-≤
        NatP.≤-refl
        (History.successfulWordEdgeCountBound word graph parsed)))
