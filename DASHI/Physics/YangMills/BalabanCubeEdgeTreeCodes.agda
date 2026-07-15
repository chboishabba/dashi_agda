module DASHI.Physics.YangMills.BalabanCubeEdgeTreeCodes where

------------------------------------------------------------------------
-- Data-level codes for CMP 109 cube-edge trees.
--
-- The code deliberately contains no proof fields.  This gives decidable
-- equality for canonical minimisation and for fibres, while validity,
-- containment, and cube-meeting remain separate predicates.  In particular
-- we do not identify proof-carrying rooted-tree records by record equality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat.Base using (_≤_; NonZero)
open import Data.Nat.Properties using (≤-refl)

open import DASHI.Physics.YangMills.GraphCombinatorics using
  ( Graph; _∈_; _∉_; NoDuplicates; Connected
  ; mapList; in-map; map-elem
  ; canonicalize; canonicalizeSound; canonicalizeComplete; canonicalizeNoDup
  ; vertexOrder; vertexOrderIsTotalOrder; TotalOrder )
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using
  ( Cube4; FaceCubeAdj; cube4Eq?; faceCubeGraph )
open import DASHI.Physics.YangMills.BalabanCubeEdgeIncidence using
  ( CubeGridVertex4; MCube4; incidentCubes
  ; incidentCubesForTreeVerticesLength≤ )

record CubeGridEdgeCode (N : Nat) : Set where
  constructor gridEdge
  field
    from to : CubeGridVertex4 N

open CubeGridEdgeCode public

GridEdgeAdmissible : ∀ {N} {{_ : NonZero N}} → CubeGridEdgeCode N → Set
GridEdgeAdmissible edge = FaceCubeAdj (from edge) (to edge)

record CubeEdgeTreeCode (N : Nat) : Set where
  constructor treeCode
  field
    root     : CubeGridVertex4 N
    vertices : List (CubeGridVertex4 N)
    edges    : List (CubeGridEdgeCode N)

open CubeEdgeTreeCode public

edgeCount : ∀ {N} → CubeEdgeTreeCode N → Nat
edgeCount T = length (edges T)

------------------------------------------------------------------------
-- Unoriented edge presentation.
--
-- The source trees are geometric and therefore do not distinguish the two
-- orientations of a grid edge.  Keeping this operation at the proof-free
-- code level is essential: a list can be duplicate-free as *oriented* data
-- while still contain both u→v and v→u.  Such a list cannot be used for an
-- exact edge-count-preserving canonical presentation.

reverseGridEdge : ∀ {N} → CubeGridEdgeCode N → CubeGridEdgeCode N
reverseGridEdge (gridEdge u v) = gridEdge v u

-- `vertexOrder` is the repository's fixed finite-code order.  The relation
-- is total, so every geometric edge has one deterministic orientation.
normaliseGridEdge : ∀ {N} {{_ : NonZero N}} →
  CubeGridEdgeCode N → CubeGridEdgeCode N
normaliseGridEdge {N} edge
  with TotalOrder.ord-total
         (vertexOrderIsTotalOrder {G = faceCubeGraph {N}})
         (from edge) (to edge)
... | inj₁ _ = edge
... | inj₂ _ = reverseGridEdge edge

-- Canonicalising edge lists needs the same generic finite-list machinery as
-- vertices.  Its adjacency is irrelevant: `canonicalize` uses only the
-- repository-wide injective vertex labelling for equality and order.
edgeCodeGraph : ∀ {N} → Graph
edgeCodeGraph {N} = record
  { Vertex = CubeGridEdgeCode N
  ; Edge = ⊥
  ; Adj = λ _ _ → ⊥
  }

canonicalVertices : ∀ {N} {{_ : NonZero N}} →
  CubeEdgeTreeCode N → List (CubeGridVertex4 N)
canonicalVertices {N} T = canonicalize {G = faceCubeGraph {N}} (vertices T)

canonicalEdges : ∀ {N} {{_ : NonZero N}} →
  CubeEdgeTreeCode N → List (CubeGridEdgeCode N)
canonicalEdges {N} T =
  canonicalize {G = edgeCodeGraph {N}}
    (mapList normaliseGridEdge (edges T))

canonicalTreeCode : ∀ {N} {{_ : NonZero N}} →
  CubeEdgeTreeCode N → CubeEdgeTreeCode N
canonicalTreeCode T =
  treeCode (root T) (canonicalVertices T) (canonicalEdges T)

canonicalTreeCode-preserves-root : ∀ {N} {{_ : NonZero N}}
  (T : CubeEdgeTreeCode N) →
  root (canonicalTreeCode T) ≡ root T
canonicalTreeCode-preserves-root T = refl

-- Canonical vertex presentation is extensional and duplicate-free.  These
-- are the first two recovery ingredients for a DFS tour: once the tour range
-- is known, it can be canonicalised and compared directly with this list.
canonicalVertices-sound : ∀ {N} {{_ : NonZero N}}
  {T : CubeEdgeTreeCode N} {v : CubeGridVertex4 N} →
  v ∈ canonicalVertices T → v ∈ vertices T
canonicalVertices-sound {N} {T} =
  canonicalizeSound {G = faceCubeGraph {N}} {xs = vertices T}

canonicalVertices-complete : ∀ {N} {{_ : NonZero N}}
  {T : CubeEdgeTreeCode N} {v : CubeGridVertex4 N} →
  v ∈ vertices T → v ∈ canonicalVertices T
canonicalVertices-complete {N} {T} =
  canonicalizeComplete {G = faceCubeGraph {N}} {xs = vertices T}

canonicalVertices-noDuplicates : ∀ {N} {{_ : NonZero N}}
  (T : CubeEdgeTreeCode N) → NoDuplicates (canonicalVertices T)
canonicalVertices-noDuplicates {N} T =
  canonicalizeNoDup {G = faceCubeGraph {N}} (vertices T)

-- Edge recovery is intentionally phrased through a pre-normalisation edge.
-- DFS later recovers `normaliseGridEdge e` from every consecutive pair, and
-- this lemma then connects that recovered canonical edge to the source code
-- without comparing proof fields.
canonicalEdges-sound : ∀ {N} {{_ : NonZero N}}
  {T : CubeEdgeTreeCode N} {e : CubeGridEdgeCode N} →
  e ∈ canonicalEdges T →
  Σ (CubeGridEdgeCode N) λ source →
    source ∈ edges T × e ≡ normaliseGridEdge source
canonicalEdges-sound {N} {T} {e} e∈canonical =
  let e∈mapped =
        canonicalizeSound {G = edgeCodeGraph {N}}
          {xs = mapList normaliseGridEdge (edges T)} e∈canonical
      sourceData = map-elem normaliseGridEdge (edges T) e∈mapped
      source = proj₁ sourceData
      e≡normalised = proj₁ (proj₂ sourceData)
      source∈ = proj₂ (proj₂ sourceData)
  in source , source∈ , e≡normalised

canonicalEdges-complete : ∀ {N} {{_ : NonZero N}}
  {T : CubeEdgeTreeCode N} (source : CubeGridEdgeCode N) →
  source ∈ edges T → normaliseGridEdge source ∈ canonicalEdges T
canonicalEdges-complete {N} {T} source source∈ =
  canonicalizeComplete {G = edgeCodeGraph {N}}
    {xs = mapList normaliseGridEdge (edges T)}
    (in-map normaliseGridEdge source∈)

canonicalEdges-noDuplicates : ∀ {N} {{_ : NonZero N}}
  (T : CubeEdgeTreeCode N) → NoDuplicates (canonicalEdges T)
canonicalEdges-noDuplicates {N} T =
  canonicalizeNoDup {G = edgeCodeGraph {N}}
    (mapList normaliseGridEdge (edges T))

------------------------------------------------------------------------
-- The graph represented by a proof-free edge code.
--
-- Cube-edge trees are geometrically unoriented.  The code stores an
-- orientation solely to make edge presentations finite data, while this
-- adjacency relation exposes either orientation to traversal and
-- connectivity proofs.  Canonical DFS later runs on this graph, never on
-- the ambient induced cube graph; therefore it cannot introduce an ambient
-- chord that is absent from the source tree.

EdgeConnects : ∀ {N} →
  List (CubeGridEdgeCode N) →
  CubeGridVertex4 N → CubeGridVertex4 N → Set
EdgeConnects {N} es u v =
  Σ (CubeGridEdgeCode N) λ e →
    e ∈ es ×
    ((from e ≡ u × to e ≡ v) ⊎ (from e ≡ v × to e ≡ u))

treeCodeGraph : ∀ {N} → CubeEdgeTreeCode N → Graph
treeCodeGraph {N} T = record
  { Vertex = CubeGridVertex4 N
  ; Edge = CubeGridEdgeCode N
  ; Adj = EdgeConnects {N} (edges T)
  }

------------------------------------------------------------------------
-- Decidable equality for data codes.

listEq? : ∀ {A : Set} →
  ((x y : A) → Dec (x ≡ y)) →
  (xs ys : List A) → Dec (xs ≡ ys)
listEq? eq [] [] = yes refl
listEq? eq [] (y ∷ ys) = no (λ ())
listEq? eq (x ∷ xs) [] = no (λ ())
listEq? eq (x ∷ xs) (y ∷ ys) with eq x y
... | no x≢y = no (λ { refl → x≢y refl })
... | yes refl with listEq? eq xs ys
... | no xs≢ys = no (λ { refl → xs≢ys refl })
... | yes refl = yes refl

cubeGridEdgeCodeEq? : ∀ {N} →
  (left right : CubeGridEdgeCode N) → Dec (left ≡ right)
cubeGridEdgeCodeEq? (gridEdge from₁ to₁) (gridEdge from₂ to₂)
  with cube4Eq? from₁ from₂
... | no from≢ = no (λ { refl → from≢ refl })
... | yes refl with cube4Eq? to₁ to₂
... | no to≢ = no (λ { refl → to≢ refl })
... | yes refl = yes refl

cubeEdgeTreeCodeEq? : ∀ {N} →
  (left right : CubeEdgeTreeCode N) → Dec (left ≡ right)
cubeEdgeTreeCodeEq? (treeCode root₁ vertices₁ edges₁)
  (treeCode root₂ vertices₂ edges₂)
  with cube4Eq? root₁ root₂
... | no root≢ = no (λ { refl → root≢ refl })
... | yes refl with listEq? cube4Eq? vertices₁ vertices₂
... | no vertices≢ = no (λ { refl → vertices≢ refl })
... | yes refl with listEq? cubeGridEdgeCodeEq? edges₁ edges₂
... | no edges≢ = no (λ { refl → edges≢ refl })
... | yes refl = yes refl

------------------------------------------------------------------------
-- The numeric part of a valid finite tree, isolated from graph-theoretic
-- validity.  For a genuine tree the following equality will be derived from
-- connectedness and acyclicity; keeping it separate lets the incidence
-- theorem be used immediately by any such derivation.

record TreeVertexBound {N : Nat} (T : CubeEdgeTreeCode N) : Set where
  field
    verticesNoDuplicates : NoDuplicates (vertices T)
    verticesAtMostEdgesPlusOne :
      length (vertices T) ≤ edgeCount T + 1

open TreeVertexBound public

------------------------------------------------------------------------
-- Source-facing finite-tree validity, still deliberately proof separate
-- from the code.  `treeCodeGraph` uses exactly `edges T`, so its
-- connectivity witnesses are already confined to the tree's own edge
-- graph.  The edge/vertex equality is the finite-tree numerical invariant
-- needed by both the incidence and DFS-tour entropy arguments.

record CubeEdgeTreeValidity {N : Nat} {{_ : NonZero N}}
  (T : CubeEdgeTreeCode N) : Set where
  field
    rootInVertices : root T ∈ vertices T
    verticesNoDuplicates : NoDuplicates (vertices T)
    edgesNoDuplicates : NoDuplicates (edges T)
    -- No geometric edge is presented twice with opposite orientations.
    -- This is the extra invariant needed for `canonicalEdges` to retain
    -- the exact source edge count rather than silently collapse a pair.
    unorientedEdgesNoDuplicates : ∀ {e} → e ∈ edges T →
      reverseGridEdge e ∉ edges T
    endpointsPresent : ∀ {e} → e ∈ edges T →
      from e ∈ vertices T × to e ∈ vertices T
    edgesAreGridEdges : ∀ {e} → e ∈ edges T → GridEdgeAdmissible e
    connectedOnOwnEdges : Connected (treeCodeGraph T) (vertices T)
    vertexEdgeCount : length (vertices T) ≡ edgeCount T + 1

open CubeEdgeTreeValidity public

validityToVertexBound : ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  CubeEdgeTreeValidity T → TreeVertexBound T
validityToVertexBound validity = record
  { verticesNoDuplicates = CubeEdgeTreeValidity.verticesNoDuplicates validity
  ; verticesAtMostEdgesPlusOne =
      equalityTo≤ (CubeEdgeTreeValidity.vertexEdgeCount validity)
  }
  where
  equalityTo≤ : ∀ {m n : Nat} → m ≡ n → m ≤ n
  equalityTo≤ refl = ≤-refl

treeIncidentCubes : ∀ {N} {{_ : NonZero N}} →
  CubeEdgeTreeCode N → List (MCube4 N)
treeIncidentCubes T = incidentCubes (vertices T)

treeIncidentCubesLength≤ : ∀ {N} {{_ : NonZero N}}
  (T : CubeEdgeTreeCode N) →
  TreeVertexBound T →
  length (treeIncidentCubes T) ≤ 16 * (edgeCount T + 1)
treeIncidentCubesLength≤ T bound =
  incidentCubesForTreeVerticesLength≤
    (vertices T)
    (edgeCount T)
    (verticesAtMostEdgesPlusOne bound)
