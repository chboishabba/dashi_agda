module DASHI.Mathematics.Complexity.Karp21CliqueVertexCoverExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
-- R. M. Karp, "Reducibility Among Combinatorial Problems" (1972),
-- original pp. 97-98: CLIQUE reduces to NODE COVER on the complement graph.
-- DOI: 10.1007/978-1-4684-2001-2_9.
--
-- DASHI: a constructive, carrier-polymorphic *semantic* equivalence.
-- The threshold/cardinality relation and executable graph encoding/cost
-- are separate, unpaid proof obligations. Not an NP-completeness theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR

negBool : Bool → Bool
negBool true = false
negBool false = true

-- Off-diagonal adjacency only. This definition permits any vertex carrier;
-- undirected symmetry and simple-graph encoding are checked by the caller.
Clique : ∀ {Vertex : Set} →
  (Vertex → Vertex → Bool) → (Vertex → Bool) → Set
Clique {Vertex} adjacency picked =
  ∀ u v → (u ≡ v → ⊥) →
    picked u ≡ true → picked v ≡ true →
    adjacency u v ≡ true

VertexCover : ∀ {Vertex : Set} →
  (Vertex → Vertex → Bool) → (Vertex → Bool) → Set
VertexCover {Vertex} adjacency picked =
  ∀ u v → (u ≡ v → ⊥) →
    adjacency u v ≡ true →
    (picked u ≡ true) ⊎ (picked v ≡ true)

complementAdjacency : ∀ {Vertex : Set} →
  (Vertex → Vertex → Bool) → Vertex → Vertex → Bool
complementAdjacency adjacency u v = negBool (adjacency u v)

complementSelection : ∀ {Vertex : Set} →
  (Vertex → Bool) → Vertex → Bool
complementSelection picked u = negBool (picked u)

trueAndNegationImpossible :
  ∀ b → b ≡ true → negBool b ≡ true → ⊥
trueAndNegationImpossible true _ ()
trueAndNegationImpossible false () _

cliqueToComplementCover :
  ∀ {Vertex : Set}
    (adjacency : Vertex → Vertex → Bool)
    (picked : Vertex → Bool) →
  Clique adjacency picked →
  VertexCover
    (complementAdjacency adjacency)
    (complementSelection picked)
cliqueToComplementCover adjacency picked clique u v distinct nonEdge
  with picked u | picked v
... | false | _ = inj₁ refl
... | true | false = inj₂ refl
... | true | true =
  ⊥-elim (trueAndNegationImpossible (adjacency u v)
    (clique u v distinct refl refl) nonEdge)

complementCoverToClique :
  ∀ {Vertex : Set}
    (adjacency : Vertex → Vertex → Bool)
    (picked : Vertex → Bool) →
  VertexCover
    (complementAdjacency adjacency)
    (complementSelection picked) →
  Clique adjacency picked
complementCoverToClique adjacency picked cover u v distinct pickedU pickedV
  with adjacency u v
... | true = refl
... | false with cover u v distinct refl
...   | inj₁ unpickedU =
  ⊥-elim (trueAndNegationImpossible (picked u) pickedU unpickedU)
...   | inj₂ unpickedV =
  ⊥-elim (trueAndNegationImpossible (picked v) pickedV unpickedV)

karpCliqueCoverSemanticEquivalence :
  ∀ {Vertex : Set}
    (adjacency : Vertex → Vertex → Bool)
    (picked : Vertex → Bool) →
  PR.Iff
    (Clique adjacency picked)
    (VertexCover
      (complementAdjacency adjacency)
      (complementSelection picked))
karpCliqueCoverSemanticEquivalence adjacency picked =
  PR.iff
    (cliqueToComplementCover adjacency picked)
    (complementCoverToClique adjacency picked)
