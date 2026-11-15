module DASHI.Mathematics.Complexity.Karp21CliqueComplementSameGraphWordExact where

------------------------------------------------------------------------
-- E05 (CLIQUE -> VERTEX COVER): ORIGINAL GRAPH / BINARY PAYLOAD WELD.
--
-- The prior DASHI source owns a loop-free symmetric SimpleGraph n and
-- its complementary graph, which negates ONLY off-diagonal adjacency.
-- UpperPair.allUpperPairs n owns the canonical list of unique i<j
-- finite addresses. The Golden bit-word complement owner gives the
-- exact emitted Bool payload and length/involution results.
--
-- The theorem here: canonical upper-triangle adjacency bytes of the
-- ACTUAL complementSimpleGraph equal bitwise negation of the original
-- graph's exact same upper-triangle adjacency bytes. A diagonal
-- self-loop cannot appear because the address is UpperPair n and the
-- existing upperPairNoLoop theorem supplies distinctness.
--
-- Open: full encoded graph header / k -> n-k threshold transport,
-- malformed-word totalization, binary machine clock, E05 InNP and
-- full Karp-21 network. No cost oracle or independent graph model.
--
-- Attribution: Richard M. Karp (1972); original DASHI
-- Karp21SimpleGraphComplementExact and UpperPair indexed graph owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans; sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21IndexedUpperPairBijectionExact as Pair
import DASHI.Mathematics.Complexity.Karp21CliqueVertexCoverExact as Karp
import DASHI.Mathematics.Complexity.Karp21SimpleGraphComplementExact as Simple
import DASHI.Mathematics.Complexity.Karp21CliqueComplementUpperTriangleWordExact as Binary

-- Source-owned graph selected only at off-diagonal upper-pair addresses.
encodeUpperPairAdjacencyBits :
  ∀ {n : Nat} →
  Simple.SimpleGraph n → List (Pair.UpperPair n) → Word.BitWord
encodeUpperPairAdjacencyBits graph [] = []
encodeUpperPairAdjacencyBits graph (address ∷ rest) =
  Simple.adjacency graph
    (proj₁ (Pair.endpoints address))
    (proj₂ (Pair.endpoints address))
  ∷ encodeUpperPairAdjacencyBits graph rest

canonicalUpperPairAdjacencyWord :
  ∀ {n : Nat} →
  Simple.SimpleGraph n → Word.BitWord
canonicalUpperPairAdjacencyWord {n} graph =
  encodeUpperPairAdjacencyBits graph (Pair.allUpperPairs n)

sourceBooleanNegationSame :
  (bit : Bool) →
  Karp.negBool bit ≡ Binary.negBool bit
sourceBooleanNegationSame true = refl
sourceBooleanNegationSame false = refl

sourceComplementAddressBit :
  ∀ {n : Nat}
    (graph : Simple.SimpleGraph n)
    (address : Pair.UpperPair n) →
  Simple.adjacency (Simple.complementSimpleGraph graph)
    (proj₁ (Pair.endpoints address))
    (proj₂ (Pair.endpoints address))
    ≡
  Binary.negBool
    (Simple.adjacency graph
      (proj₁ (Pair.endpoints address))
      (proj₂ (Pair.endpoints address)))
sourceComplementAddressBit graph address =
  trans
    (Simple.simpleComplementOffDiagonal graph
      (proj₁ (Pair.endpoints address))
      (proj₂ (Pair.endpoints address))
      (Pair.upperPairNoLoop address))
    (sourceBooleanNegationSame
      (Simple.adjacency graph
        (proj₁ (Pair.endpoints address))
        (proj₂ (Pair.endpoints address))))

sourceComplementWordSameBytes :
  ∀ {n : Nat}
    (graph : Simple.SimpleGraph n)
    (addresses : List (Pair.UpperPair n)) →
  encodeUpperPairAdjacencyBits
    (Simple.complementSimpleGraph graph) addresses
    ≡ Binary.complementUpperTriangleWord
        (encodeUpperPairAdjacencyBits graph addresses)
sourceComplementWordSameBytes graph [] = refl
sourceComplementWordSameBytes graph (address ∷ rest) =
  cong₂ _∷_
    (sourceComplementAddressBit graph address)
    (sourceComplementWordSameBytes graph rest)

-- Terminal same-object binary payload on the ORIGINAL finite simple
-- graph, with exactly the existing canonical upper-triangle order.
e05CanonicalComplementGraphWordSameObject :
  ∀ {n : Nat} (graph : Simple.SimpleGraph n) →
  canonicalUpperPairAdjacencyWord
    (Simple.complementSimpleGraph graph)
    ≡ Binary.complementUpperTriangleWord
        (canonicalUpperPairAdjacencyWord graph)
e05CanonicalComplementGraphWordSameObject {n} graph =
  sourceComplementWordSameBytes graph (Pair.allUpperPairs n)

e05CanonicalComplementGraphWordPreservesBits :
  ∀ {n : Nat} (graph : Simple.SimpleGraph n) →
  Word.encodingSize
    (canonicalUpperPairAdjacencyWord
      (Simple.complementSimpleGraph graph))
    ≡ Word.encodingSize (canonicalUpperPairAdjacencyWord graph)
e05CanonicalComplementGraphWordPreservesBits graph
  rewrite e05CanonicalComplementGraphWordSameObject graph =
  Binary.complementUpperTrianglePreservesLength
    (canonicalUpperPairAdjacencyWord graph)
