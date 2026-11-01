module DASHI.Mathematics.Complexity.Karp21WeightedCutObjectiveExact where

------------------------------------------------------------------------
-- ORIGINAL OWNERS / SOURCE ROOTS
-- Karp (1972), "Reducibility Among Combinatorial Problems",
-- DOI 10.1007/978-1-4684-2001-2_9: weighted threshold MAX CUT.
-- Goemans-Williamson (1995): separate SDP approximation framework.
--
-- DASHI contribution: a generic finite edge-list cut objective and
-- *proved* invariance under global reversal of every vertex label.
-- The weight type is abstract, so this handles signed integer weights when
-- instantiated with integer addition, as well as natural/nonnegative weights.
-- This is NOT an NP-hardness, approximation, or Ford-Fulkerson theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _,_)

import DASHI.Mathematics.Complexity.Karp21CliqueVertexCoverExact as Graph

record WeightedEdge (Vertex Weight : Set) : Set where
  constructor weightedEdge
  field
    source target : Vertex
    weight : Weight

open WeightedEdge public

differentLabels : Bool → Bool → Bool
differentLabels true true = false
differentLabels false false = false
differentLabels true false = true
differentLabels false true = true

flipDifferentLabels : ∀ left right →
  differentLabels (Graph.negBool left) (Graph.negBool right) ≡
  differentLabels left right
flipDifferentLabels true true = refl
flipDifferentLabels true false = refl
flipDifferentLabels false true = refl
flipDifferentLabels false false = refl

cutObjective :
  ∀ {Vertex Weight : Set} →
  Weight → (Weight → Weight → Weight) →
  List (WeightedEdge Vertex Weight) →
  (Vertex → Bool) → Weight
cutObjective zero combine [] side = zero
cutObjective zero combine (edge ∷ edges) side
  with differentLabels (side (source edge)) (side (target edge))
... | true = combine (weight edge) (cutObjective zero combine edges side)
... | false = cutObjective zero combine edges side

mapEquality : ∀ {A B : Set} {x y : A} →
  (f : A → B) → x ≡ y → f x ≡ f y
mapEquality f refl = refl

reverseEquality : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
reverseEquality refl = refl

transportPredicate : ∀ {A : Set} {x y : A} →
  (P : A → Set) → x ≡ y → P x → P y
transportPredicate P refl evidence = evidence

cutObjectiveFlip :
  ∀ {Vertex Weight : Set}
    (zero : Weight) (combine : Weight → Weight → Weight)
    (edges : List (WeightedEdge Vertex Weight))
    (side : Vertex → Bool) →
  cutObjective zero combine edges (Graph.complementSelection side) ≡
  cutObjective zero combine edges side
cutObjectiveFlip zero combine [] side = refl
cutObjectiveFlip zero combine (edge ∷ edges) side
  with side (source edge) | side (target edge)
... | true | true =
  cutObjectiveFlip zero combine edges side
... | true | false =
  mapEquality (combine (weight edge))
    (cutObjectiveFlip zero combine edges side)
... | false | true =
  mapEquality (combine (weight edge))
    (cutObjectiveFlip zero combine edges side)
... | false | false =
  cutObjectiveFlip zero combine edges side

-- The comparison may represent >= for signed Karp weights, or a different
-- target notion. The exact threshold predicate is supplied by the consumer.
ThresholdCut :
  ∀ {Vertex Weight : Set} →
  Weight → (Weight → Weight → Weight) →
  List (WeightedEdge Vertex Weight) →
  (Weight → Weight → Set) → Weight → Set
ThresholdCut {Vertex} zero combine edges atLeast threshold =
  Σ (Vertex → Bool)
    (λ side → atLeast (cutObjective zero combine edges side) threshold)

flipThresholdCut :
  ∀ {Vertex Weight : Set}
    (zero : Weight) (combine : Weight → Weight → Weight)
    (edges : List (WeightedEdge Vertex Weight))
    (atLeast : Weight → Weight → Set) (threshold : Weight) →
  ThresholdCut zero combine edges atLeast threshold →
  ThresholdCut zero combine edges atLeast threshold
flipThresholdCut zero combine edges atLeast threshold (side , accepted) =
  Graph.complementSelection side ,
  transportPredicate
    (λ value → atLeast value threshold)
    (reverseEquality (cutObjectiveFlip zero combine edges side))
    accepted
