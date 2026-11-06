module DASHI.Mathematics.Complexity.Karp21FinFreeOriginalWordComparisonBoundExact where

------------------------------------------------------------------------
-- ORIGINAL N21 INPUT-WORD QUADRATIC COMPARISON COUNT.
--
-- This proof joins the original successful raw-graph reader, its exact
-- 2m <= encoded input bit length witness, and the original exact
-- 2*m*(m-1) full-history address-comparison count.
--
-- It bounds the NUMBER of endpoint comparisons against the length of
-- the ACTUAL parsed gamma graph word (not declared unary vertexCount).
-- It does NOT charge each comparison in binary tape steps or claim an
-- unconditional PR.polynomialTimeVerifier: those are separate gates.
--
-- Attribution: Karp (1972), Elias gamma, original DASHI N21 owners.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_; _+_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (length)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Maybe.Base using (just)
import Data.Nat.Properties as NatP

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21FinFreeRawSparseWordVerifierExact as Runtime
import DASHI.Mathematics.Complexity.Karp21FinFreeRawReaderSparseBudgetExact as Budget
import DASHI.Mathematics.Complexity.Karp21SparseEndpointCutCertificateExact as Sparse
import DASHI.Mathematics.Complexity.Karp21FinFreePairwiseQuadraticCountExact as Count

-- Sparse.twoPerEdge is the original recursive 2-bit-per-edge function.
edgeCountBelowSparseBitCount :
  (m : Nat) → m ≤ Sparse.twoPerEdge m
edgeCountBelowSparseBitCount zero = z≤n
edgeCountBelowSparseBitCount (suc m) =
  s≤s (NatP.≤-step (edgeCountBelowSparseBitCount m))

-- Exact original recursive comparison count is nondecreasing.
comparisonCountMonotone :
  ∀ {m n : Nat} → m ≤ n →
  Count.maxAddressComparisons m ≤ Count.maxAddressComparisons n
comparisonCountMonotone z≤n = z≤n
comparisonCountMonotone (s≤s m≤n) =
  NatP.+-mono-≤
    (comparisonCountMonotone m≤n)
    (NatP.*-mono-≤ NatP.≤-refl m≤n)

-- The original parser's 2m <= |word| suffices to pay m <= |word|.
successfulWordEdgeCountBound :
  (word : Word.BitWord)
  (graph : Runtime.ParsedRawGraph) →
  Runtime.readRawGraphWord word ≡ just graph →
  length (Runtime.rawEdges graph) ≤ Word.encodingSize word
successfulWordEdgeCountBound word graph success =
  NatP.≤-trans
    (edgeCountBelowSparseBitCount
      (length (Runtime.rawEdges graph)))
    (Budget.actualFinFreeRawGraphSuccessHasSparseBudget
      word graph success)

-- Actual N21 endpoint equality *call count* is at most that of a
-- quadratic function of the literal input bit length.
successfulWordComparisonBound :
  (word : Word.BitWord)
  (graph : Runtime.ParsedRawGraph) →
  Runtime.readRawGraphWord word ≡ just graph →
  Count.maxAddressComparisons (length (Runtime.rawEdges graph))
    ≤ Count.maxAddressComparisons (Word.encodingSize word)
successfulWordComparisonBound word graph success =
  comparisonCountMonotone
    (successfulWordEdgeCountBound word graph success)

-- The original closed exact expression, now evaluated at input size.
comparisonPolynomial : Nat → Nat
comparisonPolynomial n = Count.maxAddressComparisons n

comparisonPolynomialClosed :
  (n : Nat) →
  comparisonPolynomial n ≡ 2 * n * (n NatP.∸ suc zero)
comparisonPolynomialClosed = Count.maxAddressComparisonsClosed
