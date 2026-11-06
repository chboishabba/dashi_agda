module DASHI.Mathematics.Complexity.Karp21FinFreeOriginalGraphComparisonEnvelopeExact where

------------------------------------------------------------------------
-- K05 ORIGINAL successful N21 graph word:
-- BOTH raw validator comparison count AND endpoint-consistency scans.
--
-- This closes the source-owned composition:
--   raw validator: at most 5m primitive comparisons on original raw edges;
--   endpoint history: exactly 2m(m-1) potential comparisons;
--   original successful gamma input-word: 2m <= |word|.
--
-- Thus the whole selected pair/endpoint COMPARISON COUNT is bounded
-- by the explicit quadratic expression C(L) + 5L for input bit length
-- L. Binary arithmetic and parsing work are NOT included.
-- No cost oracle, alternative graph decoder or synthetic language.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (subst; trans)
open import Data.Nat.Tactic.RingSolver using (solve)
open import Data.List.Base using (length)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Maybe.Base using (just)
open import Data.Product using (proj₂)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21GammaZigzagGraphWordDecodeExact as Graph
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21FinFreeRawValidatorComparisonCountExact as Validate
import DASHI.Mathematics.Complexity.Karp21FinFreeOriginalWordComparisonBoundExact as History
import DASHI.Core.EfficientRecoverableQuotientExact as ERQ
import DASHI.Mathematics.Complexity.PolynomialBoundClosureExact as Poly

comparisonCountForParsedGraph : Runtime.ParsedRawGraph → Nat
comparisonCountForParsedGraph graph =
  History.comparisonPolynomial (length (Runtime.rawEdges graph))
  + 5 * length (Runtime.rawEdges graph)

actualValidatedComparisonCount : Runtime.ParsedRawGraph → Nat
actualValidatedComparisonCount graph =
  History.comparisonPolynomial (length (Runtime.rawEdges graph))
  + proj₂
      (Validate.countedRawValidatorPrimitive
        (Runtime.rawVertices graph)
        Graph.noPrevious
        (Runtime.rawEdges graph))


-- First account for the original validator's exact observed count,
-- not a presumed constant-time check per edge.
actualComparisonCountBelowSchedule :
  (graph : Runtime.ParsedRawGraph) →
  actualValidatedComparisonCount graph ≤ comparisonCountForParsedGraph graph
actualComparisonCountBelowSchedule graph =
  NatP.+-mono-≤
    NatP.≤-refl
    (Validate.primitiveValidatorCountBound
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
      + 5 * Word.encodingSize word
successfulOriginalGraphCombinedComparisonBound word graph parsed =
  NatP.≤-trans
    (actualComparisonCountBelowSchedule graph)
    (NatP.+-mono-≤
      (History.successfulWordComparisonBound word graph parsed)
      (NatP.*-mono-≤
        NatP.≤-refl
        (History.successfulWordEdgeCountBound word graph parsed)))

------------------------------------------------------------------------
-- Native DASHI degree-two polynomial certificate on the combined
-- ORIGINAL comparator-operation count C(L) + 5L.
------------------------------------------------------------------------

positiveNatAtMostSquare : (n : Nat) → n ≤ n * n
positiveNatAtMostSquare zero = NatP.≤-refl
positiveNatAtMostSquare (suc n) =
  subst (λ lower → lower ≤ suc n * suc n)
    (NatP.*-identityʳ (suc n))
    (NatP.*-mono-≤
      NatP.≤-refl (s≤s z≤n))


squareNativePolynomial :
  ERQ.PolynomialBound (λ n → n * n)
squareNativePolynomial =
  Poly.productPolynomialBound
    History.identityPolynomial History.identityPolynomial

squareAtMostNativePow :
  (n : Nat) → n * n ≤ ERQ.pow (suc n) 2
squareAtMostNativePow n =
  subst (λ upper → n * n ≤ upper)
    (NatP.*-identityˡ (ERQ.pow (suc n) 2))
    (ERQ.bounded squareNativePolynomial n)

natBelowSquaredPolynomial :
  (n : Nat) → n ≤ ERQ.pow (suc n) 2
natBelowSquaredPolynomial n =
  NatP.≤-trans
    (positiveNatAtMostSquare n)
    (squareAtMostNativePow n)

sevenFactorIdentity :
  (x : Nat) → 2 * x + 5 * x ≡ 7 * x
sevenFactorIdentity x = solve (x ∷ [])

combinedComparisonPolynomial : Nat → Nat
combinedComparisonPolynomial n = History.comparisonPolynomial n + 5 * n

combinedComparisonPolynomialBound :
  ERQ.PolynomialBound combinedComparisonPolynomial
combinedComparisonPolynomialBound =
  ERQ.polynomialBound 7 2
    (λ n →
      subst
        (λ upper → combinedComparisonPolynomial n ≤ upper)
        (sevenFactorIdentity (ERQ.pow (suc n) 2))
        (NatP.+-mono-≤
          (ERQ.bounded History.comparisonPolynomialBound n)
          (NatP.*-mono-≤
            NatP.≤-refl (natBelowSquaredPolynomial n))))

originalSuccessfulWordCombinedPolynomialClock :
  (word : Word.BitWord)
  (graph : Runtime.ParsedRawGraph) →
  Runtime.readRawGraphWord word ≡ just graph →
  actualValidatedComparisonCount graph ≤
    ERQ.coefficient combinedComparisonPolynomialBound *
      ERQ.pow (suc (Word.encodingSize word))
        (ERQ.exponent combinedComparisonPolynomialBound)
originalSuccessfulWordCombinedPolynomialClock word graph parsed =
  NatP.≤-trans
    (successfulOriginalGraphCombinedComparisonBound word graph parsed)
    (ERQ.bounded combinedComparisonPolynomialBound
      (Word.encodingSize word))
