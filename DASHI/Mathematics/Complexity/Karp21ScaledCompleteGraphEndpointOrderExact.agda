module DASHI.Mathematics.Complexity.Karp21ScaledCompleteGraphEndpointOrderExact where

------------------------------------------------------------------------
-- E20: endpoint validity on the ORIGINAL scaled complete graph.
--
-- Every edge of Gen.completeScaledPairEdges source is exactly an
-- upper-triangular address p in Pair.allUpperPairs n, not an
-- independent graph constructor. This source-written lemma proves
--
--             toℕ first(edge) < toℕ second(edge) < n
--
-- for ALL emitted edges and arbitrary signed source coefficients.
-- Scaling by four affects only signed weight, never endpoints.
-- No postulate, surrogate graph or source-witness access.
--
-- Stronger global lexicographic adjacency remains a separate gate;
-- full validator/encoder/decoder same-object and machine clocks OPEN.
--
-- Credit: Karp (1972), DASHI complete-graph and UpperPair owners.
-- Agda kernel acceptance has NOT been performed on this source.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_<_; z≤n; s≤s)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Base using (List; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (cong; sym)

import Data.Fin.Base as Fin
import Data.Vec.Base as Vec
open import Data.Integer.Base using (ℤ)

import DASHI.Mathematics.Complexity.Karp21FiniteWeightedMaxCutVerifierExact as Cut
import DASHI.Mathematics.Complexity.Karp21IndexedUpperPairBijectionExact as Pair
import DASHI.Mathematics.Complexity.Karp21UpperPairGraphEnumerationExact as Enum
import DASHI.Mathematics.Complexity.Karp21FiniteCompleteGraphGeneratorExact as Gen
import DASHI.Mathematics.Complexity.Karp21SignedGraphScaleAndAppendExact as Scale

------------------------------------------------------------------------
-- Numeric order is established by structural Fin and UpperPair
-- induction, rather than a conjectured external decidable comparator.
------------------------------------------------------------------------

finIndexInRange :
  ∀ {n : Nat} (vertex : Fin.Fin n) →
  Fin.toℕ vertex < n
finIndexInRange Fin.zero = s≤s z≤n
finIndexInRange (Fin.suc vertex) =
  s≤s (finIndexInRange vertex)

upperPairFirstLessSecond :
  ∀ {n : Nat} (pair : Pair.UpperPair n) →
  Fin.toℕ (proj₁ (Pair.endpoints pair))
    < Fin.toℕ (proj₂ (Pair.endpoints pair))
upperPairFirstLessSecond (Pair.headTail j) = s≤s z≤n
upperPairFirstLessSecond (Pair.tailPair p) =
  s≤s (upperPairFirstLessSecond p)

upperPairSecondWithinVertices :
  ∀ {n : Nat} (pair : Pair.UpperPair n) →
  Fin.toℕ (proj₂ (Pair.endpoints pair)) < n
upperPairSecondWithinVertices pair =
  finIndexInRange (proj₂ (Pair.endpoints pair))

------------------------------------------------------------------------
-- The exact prior edgeAtUpperPair source owner emits the same typed
-- endpoints as Pair.endpoints; its weight may be any signed integer.
------------------------------------------------------------------------

edgeAtAddressFirstSame :
  ∀ {n : Nat} (source : Vec.Vec ℤ n)
    (pair : Pair.UpperPair n) →
  Cut.first (Enum.edgeAtUpperPair source pair)
    ≡ proj₁ (Pair.endpoints pair)
edgeAtAddressFirstSame Vec.[] ()
edgeAtAddressFirstSame (x Vec.∷ rest) (Pair.headTail j) = refl
edgeAtAddressFirstSame (x Vec.∷ rest) (Pair.tailPair pair) =
  cong Fin.suc (edgeAtAddressFirstSame rest pair)

edgeAtAddressSecondSame :
  ∀ {n : Nat} (source : Vec.Vec ℤ n)
    (pair : Pair.UpperPair n) →
  Cut.second (Enum.edgeAtUpperPair source pair)
    ≡ proj₂ (Pair.endpoints pair)
edgeAtAddressSecondSame Vec.[] ()
edgeAtAddressSecondSame (x Vec.∷ rest) (Pair.headTail j) = refl
edgeAtAddressSecondSame (x Vec.∷ rest) (Pair.tailPair pair) =
  cong Fin.suc (edgeAtAddressSecondSame rest pair)

------------------------------------------------------------------------
-- A source-generated edge is valid for the real N21 parser's
-- per-edge u<v<n checks. The graph's signed 4x scaling preserves it.
------------------------------------------------------------------------

CanonicalEdgeEndpoints :
  ∀ {n : Nat} → Cut.SignedUndirectedEdge n → Set
CanonicalEdgeEndpoints {n} edge =
  (Fin.toℕ (Cut.first edge) < Fin.toℕ (Cut.second edge))
  × (Fin.toℕ (Cut.second edge) < n)

scaledAddressCanonicalEndpoints :
  ∀ {n : Nat} (source : Vec.Vec ℤ n)
    (pair : Pair.UpperPair n) →
  CanonicalEdgeEndpoints
    (Scale.scaleEdgeWeightFour (Enum.edgeAtUpperPair source pair))
scaledAddressCanonicalEndpoints source pair
  rewrite cong Fin.toℕ (edgeAtAddressFirstSame source pair)
        | cong Fin.toℕ (edgeAtAddressSecondSame source pair) =
  upperPairFirstLessSecond pair ,
  upperPairSecondWithinVertices pair

data AllCanonicalEdgeEndpoints {n : Nat} :
  List (Cut.SignedUndirectedEdge n) → Set where
  canonicalNil : AllCanonicalEdgeEndpoints []
  canonicalCons :
    ∀ {head rest} →
    CanonicalEdgeEndpoints head →
    AllCanonicalEdgeEndpoints rest →
    AllCanonicalEdgeEndpoints (head ∷ rest)

canonicalScaledEnumeratedPairs :
  ∀ {n : Nat} (source : Vec.Vec ℤ n)
    (pairs : List (Pair.UpperPair n)) →
  AllCanonicalEdgeEndpoints
    (map (λ p → Scale.scaleEdgeWeightFour
      (Enum.edgeAtUpperPair source p)) pairs)
canonicalScaledEnumeratedPairs source [] = canonicalNil
canonicalScaledEnumeratedPairs source (pair ∷ rest) =
  canonicalCons
    (scaledAddressCanonicalEndpoints source pair)
    (canonicalScaledEnumeratedPairs source rest)

-- This is about the SAME weighted edge list as E20's original map,
-- using the previously proved upper-triangle enumeration equality.
sourceIndexedScaledCompleteGraphEndpoints :
  ∀ {n : Nat} (source : Vec.Vec ℤ n) →
  AllCanonicalEdgeEndpoints (Gen.completeScaledPairEdges source)
sourceIndexedScaledCompleteGraphEndpoints {n} source
  rewrite Enum.actualKarpGraphCanonicalUpperPairs source
        | Enum.mapCompose
            Scale.scaleEdgeWeightFour
            (Enum.edgeAtUpperPair source)
            (Pair.allUpperPairs n) =
  canonicalScaledEnumeratedPairs source (Pair.allUpperPairs n)
