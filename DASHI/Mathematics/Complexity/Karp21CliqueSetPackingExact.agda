module DASHI.Mathematics.Complexity.Karp21CliqueSetPackingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
-- Richard M. Karp (1972), "Reducibility Among Combinatorial Problems",
-- DOI 10.1007/978-1-4684-2001-2_9, original pp. 97-98:
-- CLIQUE reduces to SET PACKING via nonedge-incidence sets.
--
-- DASHI CONTRIBUTION
-- Prove the constructive witness equivalence on an arbitrary symmetric
-- Boolean graph. The universe of set elements consists of off-diagonal
-- nonedge pairs; each vertex indexes its incidence subset. These
-- combinatorial proofs DO NOT include an executable polynomial encoding,
-- finite-cardinality bound, or NP-completeness transport.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21CliqueVertexCoverExact as CV

Symmetric : ∀ {Vertex : Set} →
  (Vertex → Vertex → Bool) → Set
Symmetric {Vertex} adjacency =
  ∀ u v → adjacency u v ≡ adjacency v u

transposeEquality : ∀ {A : Set} {a b : A} →
  a ≡ b → b ≡ a
transposeEquality refl = refl

chainEquality : ∀ {A : Set} {a b c : A} →
  a ≡ b → b ≡ c → a ≡ c
chainEquality refl proof = proof

trueCannotEqualFalse : ∀ {value : Bool} →
  value ≡ true → value ≡ false → ⊥
trueCannotEqualFalse {true} refl ()
trueCannotEqualFalse {false} () _

-- A concrete universe element is a pair of distinct vertices having no edge.
-- The subset S_u consists exactly of nonedges incident to vertex u.
NonedgeIncident : ∀ {Vertex : Set} →
  (Vertex → Vertex → Bool) → Vertex →
  (Vertex × Vertex) → Set
NonedgeIncident adjacency u (a , b) =
  ((u ≡ a) ⊎ (u ≡ b)) ×
  ((a ≡ b → ⊥) × (adjacency a b ≡ false))

-- A picked family is a packing when its distinct chosen subsets have no
-- common universe element. The same picked predicate also indexes a clique.
Packing : ∀ {Vertex : Set} →
  (Vertex → Vertex → Bool) → (Vertex → Bool) → Set
Packing {Vertex} adjacency picked =
  ∀ u v → (u ≡ v → ⊥) →
    picked u ≡ true → picked v ≡ true →
    ∀ candidate →
      NonedgeIncident adjacency u candidate →
      NonedgeIncident adjacency v candidate →
      ⊥

cliqueToPacking :
  ∀ {Vertex : Set}
    (adjacency : Vertex → Vertex → Bool)
    (picked : Vertex → Bool) →
  Symmetric adjacency →
  CV.Clique adjacency picked →
  Packing adjacency picked
cliqueToPacking adjacency picked symmetry clique u v distinct pu pv
  (a , b) (inj₁ refl , (_ , absent)) (inj₁ refl , _) =
  distinct refl
cliqueToPacking adjacency picked symmetry clique u v distinct pu pv
  (a , b) (inj₂ refl , (_ , absent)) (inj₂ refl , _) =
  distinct refl
cliqueToPacking adjacency picked symmetry clique u v distinct pu pv
  (a , b) (inj₁ refl , (_ , absent)) (inj₂ refl , _) =
  trueCannotEqualFalse (clique a b distinct pu pv) absent
cliqueToPacking adjacency picked symmetry clique u v distinct pu pv
  (a , b) (inj₂ refl , (_ , absent)) (inj₁ refl , _) =
  trueCannotEqualFalse
    (chainEquality (symmetry a b) (clique b a distinct pu pv))
    absent

packingToClique :
  ∀ {Vertex : Set}
    (adjacency : Vertex → Vertex → Bool)
    (picked : Vertex → Bool) →
  Packing adjacency picked →
  CV.Clique adjacency picked
packingToClique adjacency picked packing u v distinct pu pv
  with adjacency u v
... | true = refl
... | false = ⊥-elim
  (packing u v distinct pu pv (u , v)
    (inj₁ refl , (distinct , refl))
    (inj₂ refl , (distinct , refl)))

karpCliquePackingSemanticEquivalence :
  ∀ {Vertex : Set}
    (adjacency : Vertex → Vertex → Bool)
    (picked : Vertex → Bool) →
  Symmetric adjacency →
  PR.Iff (CV.Clique adjacency picked) (Packing adjacency picked)
karpCliquePackingSemanticEquivalence adjacency picked symmetric =
  PR.iff
    (cliqueToPacking adjacency picked symmetric)
    (packingToClique adjacency picked)
