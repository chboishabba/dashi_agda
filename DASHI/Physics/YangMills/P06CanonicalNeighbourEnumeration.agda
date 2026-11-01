module DASHI.Physics.YangMills.P06CanonicalNeighbourEnumeration where

------------------------------------------------------------------------
-- Canonical refinement of a bounded neighbour enumeration.
--
-- The raw enumeration remains the only input.  Each neighbour list is
-- canonicalized (sorted and duplicate-free), while soundness and
-- completeness are transported through the existing canonicalize API.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; length)
open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-trans)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC
  using ( Graph
        ; BoundedNeighbourEnumeration
        ; CanonicalBoundedNeighbourEnumeration
        ; NoDuplicates
        ; Sorted
        ; _∈_
        ; _⊆_
        ; canonicalize
        ; canonicalizeNoDup
        ; canonicalizeSorted
        ; canonicalizeSound
        ; canonicalizeComplete
        ; noDupSubsetLength≤
        ; vertexOrder
        )

------------------------------------------------------------------------
-- The exact list-length lemma needed by the bounded wrapper.
------------------------------------------------------------------------

canonicalizeSubset :
  {G : Graph} (xs : List (Graph.Vertex G)) →
  canonicalize {G} xs ⊆ xs
canonicalizeSubset xs = canonicalizeSound

canonicalizeLength≤ :
  {G : Graph} (xs : List (Graph.Vertex G)) →
  length (canonicalize {G} xs) ≤ length xs
canonicalizeLength≤ {G} xs =
  noDupSubsetLength≤
    (canonicalizeNoDup {G} xs)
    (canonicalizeSubset xs)

------------------------------------------------------------------------
-- Canonicalized neighbour lists.
------------------------------------------------------------------------

canonicalNeighbours :
  {G : Graph} {Δ : ℕ} →
  BoundedNeighbourEnumeration G Δ →
  Graph.Vertex G → List (Graph.Vertex G)
canonicalNeighbours {G} BNE u =
  canonicalize {G}
    (BoundedNeighbourEnumeration.neighbours BNE u)

canonicalNeighbourSound :
  {G : Graph} {Δ : ℕ}
  (BNE : BoundedNeighbourEnumeration G Δ) →
  ∀ {u v} → v ∈ canonicalNeighbours BNE u → Graph.Adj G u v
canonicalNeighbourSound {G} BNE {u} {v} v∈ =
  BoundedNeighbourEnumeration.neighbourSound BNE
    (canonicalizeSound {G} v∈)

canonicalNeighbourComplete :
  {G : Graph} {Δ : ℕ}
  (BNE : BoundedNeighbourEnumeration G Δ) →
  ∀ {u v} → Graph.Adj G u v → v ∈ canonicalNeighbours BNE u
canonicalNeighbourComplete {G} BNE {u} {v} uv =
  canonicalizeComplete {G}
    (BoundedNeighbourEnumeration.neighbourComplete BNE uv)

canonicalNeighbourNoDup :
  {G : Graph} {Δ : ℕ}
  (BNE : BoundedNeighbourEnumeration G Δ) →
  ∀ u → NoDuplicates (canonicalNeighbours BNE u)
canonicalNeighbourNoDup BNE u =
  canonicalizeNoDup
    (BoundedNeighbourEnumeration.neighbours BNE u)

canonicalNeighbourSorted :
  {G : Graph} {Δ : ℕ}
  (BNE : BoundedNeighbourEnumeration G Δ) →
  ∀ u → Sorted (vertexOrder {G}) (canonicalNeighbours BNE u)
canonicalNeighbourSorted {G} BNE u =
  canonicalizeSorted {G}
    (BoundedNeighbourEnumeration.neighbours BNE u)

canonicalNeighbourBound :
  {G : Graph} {Δ : ℕ}
  (BNE : BoundedNeighbourEnumeration G Δ) →
  ∀ u → length (canonicalNeighbours BNE u) ≤ Δ
canonicalNeighbourBound BNE u =
  ≤-trans
    (canonicalizeLength≤
      (BoundedNeighbourEnumeration.neighbours BNE u))
    (BoundedNeighbourEnumeration.neighbourBound BNE u)

------------------------------------------------------------------------
-- Reusable packaged wrapper.
------------------------------------------------------------------------

record P06CanonicalBoundedNeighbourEnumeration
  (G : Graph) (Δ : ℕ) : Set₁ where
  field
    bounded : BoundedNeighbourEnumeration G Δ

    neighbours : Graph.Vertex G → List (Graph.Vertex G)
    neighbours-is-canonical :
      ∀ u → neighbours u ≡ canonicalNeighbours bounded u

    neighbourSound :
      ∀ {u v} → v ∈ neighbours u → Graph.Adj G u v
    neighbourComplete :
      ∀ {u v} → Graph.Adj G u v → v ∈ neighbours u
    neighbourNoDuplicates :
      ∀ u → NoDuplicates (neighbours u)
    neighbourSorted :
      ∀ u → Sorted (vertexOrder {G}) (neighbours u)
    neighbourBound :
      ∀ u → length (neighbours u) ≤ Δ

canonicalBoundedNeighbourEnumeration :
  {G : Graph} {Δ : ℕ} →
  (BNE : BoundedNeighbourEnumeration G Δ) →
  P06CanonicalBoundedNeighbourEnumeration G Δ
canonicalBoundedNeighbourEnumeration BNE = record
  { bounded = BNE
  ; neighbours = canonicalNeighbours BNE
  ; neighbours-is-canonical = λ u → refl
  ; neighbourSound = canonicalNeighbourSound BNE
  ; neighbourComplete = canonicalNeighbourComplete BNE
  ; neighbourNoDuplicates = canonicalNeighbourNoDup BNE
  ; neighbourSorted = canonicalNeighbourSorted BNE
  ; neighbourBound = canonicalNeighbourBound BNE
  }

------------------------------------------------------------------------
-- Adapter to the canonical refinement used by the recursive walk surface.
------------------------------------------------------------------------

toGraphCanonicalBoundedNeighbourEnumeration :
  {G : Graph} {Δ : ℕ} →
  P06CanonicalBoundedNeighbourEnumeration G Δ →
  CanonicalBoundedNeighbourEnumeration G Δ
toGraphCanonicalBoundedNeighbourEnumeration E =
  record
  { bounded = record
      { neighbours = P06CanonicalBoundedNeighbourEnumeration.neighbours E
      ; neighbourSound =
          P06CanonicalBoundedNeighbourEnumeration.neighbourSound E
      ; neighbourComplete =
          P06CanonicalBoundedNeighbourEnumeration.neighbourComplete E
      ; neighbourBound =
          P06CanonicalBoundedNeighbourEnumeration.neighbourBound E
      }
  ; neighboursNoDuplicates =
      P06CanonicalBoundedNeighbourEnumeration.neighbourNoDuplicates E
  }
