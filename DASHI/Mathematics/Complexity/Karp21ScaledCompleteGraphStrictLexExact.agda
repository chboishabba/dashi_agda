module DASHI.Mathematics.Complexity.Karp21ScaledCompleteGraphStrictLexExact where

------------------------------------------------------------------------
-- E20: GLOBAL STRICT LEX ORDER ON THE ACTUAL SCALED EDGE LIST.
--
-- Original UpperPair addresses are in strict structural order.
-- Their Fin endpoint projection is a genuine numeric lex order;
-- multiplying signed edge weights by four preserves both endpoints.
--
-- Every earlier emitted edge therefore precedes every later edge in
-- lexicographic (u,v) order, not merely "no duplicates". This source
-- theorem uses the original completeScaledPairEdges and original
-- UpperPair enumeration; there is no alternate output graph.
--
-- The original concrete parser's Bool strictAfter equivalence,
-- proof-carrying Fin.fromℕ< reconstruction, threshold and clocks
-- remain separate obligations.
--
-- Original Karp (1972); DASHI UpperPair/complete-graph prior owners.
-- Source-written only, NOT accepted by Agda kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_; z≤n; s≤s)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong)
open import Data.List.Base using (List; map)
import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
open import Data.Integer.Base using (ℤ)

import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21IndexedUpperPairBijectionExact as Pair
import DASHI.Mathematics.Complexity.Karp21UpperPairGraphEnumerationExact as Enum
import DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphGeneratorExact as Gen
import DASHI.Mathematics.Complexity.Karp21SignedGraphScaleAndAppendExact as Scale
import DASHI.Mathematics.Complexity.Karp21ScaledCompleteGraphEndpointOrderExact as Bounds
import DASHI.Mathematics.Complexity.Karp21UpperPairStructuralLexOrderExact as Lex

------------------------------------------------------------------------
-- Numeric lexicographic relation, not a syntactic address relation.
------------------------------------------------------------------------

NumericLexBefore :
  ∀ {n : Nat} →
  (Fin.Fin n × Fin.Fin n) →
  (Fin.Fin n × Fin.Fin n) → Set
NumericLexBefore a b =
  (Fin.toℕ (proj₁ a) < Fin.toℕ (proj₁ b))
  ⊎
  ((Fin.toℕ (proj₁ a) ≡ Fin.toℕ (proj₁ b))
    × (Fin.toℕ (proj₂ a) < Fin.toℕ (proj₂ b)))

-- Prove the structural order corresponds to ordinary numeric lex
-- comparison on the original addressed endpoints.
upperPairBeforeNumeric :
  ∀ {n : Nat} {p q : Pair.UpperPair n} →
  Lex.UpperPairBefore p q →
  NumericLexBefore (Pair.endpoints p) (Pair.endpoints q)
upperPairBeforeNumeric (Lex.headBeforeHead smaller) =
  inj₂ (refl , s≤s smaller)
upperPairBeforeNumeric Lex.headBeforeTail =
  inj₁ (s≤s z≤n)
upperPairBeforeNumeric (Lex.tailBeforeTail earlier)
  with upperPairBeforeNumeric earlier
... | inj₁ firstBefore = inj₁ (s≤s firstBefore)
... | inj₂ (sameFirst , secondBefore) =
  inj₂ (cong suc sameFirst , s≤s secondBefore)

------------------------------------------------------------------------
-- Same signed edges and same original scaled graph. Only the endpoint
-- projection is used to compare them; weights remain unaltered.
------------------------------------------------------------------------

CanonicalEdgeNumericBefore :
  ∀ {n : Nat} →
  Cut.SignedUndirectedEdge n →
  Cut.SignedUndirectedEdge n → Set
CanonicalEdgeNumericBefore first second =
  (Fin.toℕ (Cut.first first) < Fin.toℕ (Cut.first second))
  ⊎
  ((Fin.toℕ (Cut.first first) ≡ Fin.toℕ (Cut.first second))
    × (Fin.toℕ (Cut.second first) < Fin.toℕ (Cut.second second)))

scaledAddressNumericBefore :
  ∀ {n : Nat} (source : Vec.Vec ℤ n)
    {p q : Pair.UpperPair n} →
  Lex.UpperPairBefore p q →
  CanonicalEdgeNumericBefore
    (Scale.scaleEdgeWeightFour (Enum.edgeAtUpperPair source p))
    (Scale.scaleEdgeWeightFour (Enum.edgeAtUpperPair source q))
scaledAddressNumericBefore source {p} {q} earlier
  rewrite cong Fin.toℕ (Bounds.edgeAtAddressFirstSame source p)
        | cong Fin.toℕ (Bounds.edgeAtAddressFirstSame source q)
        | cong Fin.toℕ (Bounds.edgeAtAddressSecondSame source p)
        | cong Fin.toℕ (Bounds.edgeAtAddressSecondSame source q) =
  upperPairBeforeNumeric earlier

------------------------------------------------------------------------
-- The existing generic globally-sorted list transformer retains the
-- strong condition: each earlier edge is before EVERY later edge.
------------------------------------------------------------------------

sourceIndexedScaledCompleteGraphStrictLex :
  ∀ {n : Nat} (source : Vec.Vec ℤ n) →
  Lex.StrictSorted CanonicalEdgeNumericBefore
    (Gen.completeScaledPairEdges source)
sourceIndexedScaledCompleteGraphStrictLex {n} source
  rewrite Enum.actualKarpGraphCanonicalUpperPairs source
        | Enum.mapCompose
            Scale.scaleEdgeWeightFour
            (Enum.edgeAtUpperPair source)
            (Pair.allUpperPairs n) =
  Lex.mapStrictSorted
    (λ p → Scale.scaleEdgeWeightFour (Enum.edgeAtUpperPair source p))
    (scaledAddressNumericBefore source)
    (Pair.allUpperPairs n)
    (Lex.allUpperPairsStrictLexOrder n)
