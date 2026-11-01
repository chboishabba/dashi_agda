module DASHI.Mathematics.Complexity.Karp21VertexSetCoverIncidenceExact where

------------------------------------------------------------------------
-- SOURCE: Karp (1972), pp. 97-98, NODE COVER -> SET COVERING.
-- DOI: 10.1007/978-1-4684-2001-2_9.
-- DASHI: true constructive forward/backward witness transport on edge
-- incidence, not a concrete encoded polynomial-time graph transformation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.Karp21CliqueVertexCoverExact as CV

-- Select an index (=vertex) whose incident-edge set covers each
-- enumerated graph edge. The incident universe is indexed by endpoints.
IndexedEdgeSetCover :
  ∀ {Vertex : Set} →
  (Vertex → Vertex → Bool) → (Vertex → Bool) → Set
IndexedEdgeSetCover {Vertex} adjacent picked =
  ∀ edge →
    ((proj₁ edge ≡ proj₂ edge → ⊥) ×
      adjacent (proj₁ edge) (proj₂ edge) ≡ true) →
    Σ Vertex (λ selected →
      (picked selected ≡ true) ×
      ((selected ≡ proj₁ edge) ⊎ (selected ≡ proj₂ edge)))

vertexCoverToIndexedSetCover :
  ∀ {Vertex : Set}
    (adjacent : Vertex → Vertex → Bool)
    (picked : Vertex → Bool) →
  CV.VertexCover adjacent picked →
  IndexedEdgeSetCover adjacent picked
vertexCoverToIndexedSetCover adjacent picked cover
    (u , v) (distinct , connected)
  with cover u v distinct connected
... | inj₁ selectedU = u , (selectedU , inj₁ refl)
... | inj₂ selectedV = v , (selectedV , inj₂ refl)

indexedSetCoverToVertexCover :
  ∀ {Vertex : Set}
    (adjacent : Vertex → Vertex → Bool)
    (picked : Vertex → Bool) →
  IndexedEdgeSetCover adjacent picked →
  CV.VertexCover adjacent picked
indexedSetCoverToVertexCover adjacent picked cover u v distinct connected
  with cover (u , v) (distinct , connected)
... | selected , (chosen , inj₁ refl) = inj₁ chosen
... | selected , (chosen , inj₂ refl) = inj₂ chosen

karpNodeCoverSetCoverWitnessIff :
  ∀ {Vertex : Set}
    (adjacent : Vertex → Vertex → Bool)
    (picked : Vertex → Bool) →
  PR.Iff
    (CV.VertexCover adjacent picked)
    (IndexedEdgeSetCover adjacent picked)
karpNodeCoverSetCoverWitnessIff adjacent picked =
  PR.iff
    (vertexCoverToIndexedSetCover adjacent picked)
    (indexedSetCoverToVertexCover adjacent picked)
