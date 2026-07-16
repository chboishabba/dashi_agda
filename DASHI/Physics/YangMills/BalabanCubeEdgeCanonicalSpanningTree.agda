module DASHI.Physics.YangMills.BalabanCubeEdgeCanonicalSpanningTree where

------------------------------------------------------------------------
-- Constructive spanning-tree view of a valid CMP 109 cube-edge code.
--
-- The ambient graph here is deliberately `treeCodeGraph T`, not the
-- induced face-cube graph on its vertices.  Consequently every edge used by
-- the path-union construction is an edge already present in the proof-free
-- source code; no geometric chord can be introduced at this boundary.
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; NonZero; zero; suc; _∸_; _+_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; _∷_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC using
  ( _∈_
  ; _⊆_
  ; ConsecutiveEdges
  ; NoDuplicates
  ; mapList
  ; map-elem
  ; in-map
  ; mapList-noDup-by-projection
  ; noDupSubsetEqualLengthSameVertexSet
  ; canonicalize
  ; canonicalizeNoDup
  ; listMapLength
  ; RootedConnectedSkeleton
  ; SameVertexSet
  ; sameVertexSet-trans
  ; CanonicalVertexList
  ; canonicalizeSound
  ; canonicalizeComplete
  ; canonicalizeSorted
  )
open import DASHI.Physics.YangMills.P06ConstructiveSpanningTreeDFS as CDFS
  using ( SkeletonAdjacencySymmetry
        ; RootedPathConnected
        ; RootedTreeNode
        ; ConstructiveRootedSpanningTree
        ; DFSTourInvariant
        ; dfsTour
        ; rootedConnectedSkeletonToRootedPathConnected
        ; dfsTourInvariant
        ; constructiveTreeRangeIs
        )
open import DASHI.Physics.YangMills.P06PathUnionSpanningTreeClosure as PU
  using ( ParentLink
        ; CompleteInsertionParentTree
        ; pathUnionFoldToCompleteInsertionTree
        ; completeInsertionTreeToConstructiveRootedSpanningTree
        ; linksLength
        ; insertionChildrenNoDuplicates
        ; AppearsBefore
        ; historyParentBeforeChild
        ; appearsBeforeAsymmetric
        )
open import DASHI.Physics.YangMills.P06FaceCubeTorusGeometry using
  ( FaceCubeAdj; faceCubeAdjSymmetric; faceCubeGraph )
open import DASHI.Physics.YangMills.BalabanCubeEdgeTreeCodes public
open import DASHI.Physics.YangMills.BalabanCubeEdgeIncidence using
  ( CubeGridVertex4 )
open import DASHI.Physics.YangMills.BalabanCubeEdgeDFSTour using
  ( adjacentPairs
  ; tourCanonicalVertices; tourCanonicalVertices-noDuplicates
  ; tourCanonicalEdges
  )

------------------------------------------------------------------------
-- Own-edge symmetry is data-level: an `EdgeConnects` witness is reused with
-- the opposite orientation branch.  Membership in the carrier is retained
-- in the interface for the benefit of the generic path-union API, but is not
-- needed to manufacture the reverse code edge.

treeCodeGraphSymmetry :
  ∀ {N} {{_ : NonZero N}} (T : CubeEdgeTreeCode N) →
  SkeletonAdjacencySymmetry {G = treeCodeGraph T} (vertices T)
treeCodeGraphSymmetry T = record
  { reverseInside = λ _ _ adjacency → reverse adjacency }
  where
  reverse : ∀ {u v} →
    GC.Graph.Adj (treeCodeGraph T) u v →
    GC.Graph.Adj (treeCodeGraph T) v u
  reverse (edge , edge∈ , inj₁ endpoints) = edge , edge∈ , inj₂ endpoints
  reverse (edge , edge∈ , inj₂ endpoints) = edge , edge∈ , inj₁ endpoints

-- Every own-edge adjacency is a source-admissible face move.  This is the
-- geometry-preservation side of the construction: the reified tree and its
-- tour may be analysed in `treeCodeGraph`, while every move still lifts to
-- the actual M-cube grid graph.
treeCodeAdjacencyIsFaceAdj :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} {u v} →
  (validity : CubeEdgeTreeValidity T) →
  GC.Graph.Adj (treeCodeGraph T) u v →
  FaceCubeAdj u v
treeCodeAdjacencyIsFaceAdj {u = u} {v = v} validity
  (edge , edge∈ , inj₁ endpoints) =
  let from≡u = proj₁ endpoints
      to≡v = proj₂ endpoints
  in subst (λ a → FaceCubeAdj a v) from≡u
       (subst (λ b → FaceCubeAdj (from edge) b) to≡v
         (edgesAreGridEdges validity edge∈))
treeCodeAdjacencyIsFaceAdj {u = u} {v = v} validity
  (edge , edge∈ , inj₂ endpoints) =
  let from≡v = proj₁ endpoints
      to≡u = proj₂ endpoints
      face-vu =
        subst (λ a → FaceCubeAdj a u) from≡v
          (subst (λ b → FaceCubeAdj (from edge) b) to≡u
            (edgesAreGridEdges validity edge∈))
  in faceCubeAdjSymmetric face-vu

validCodeRootedConnected :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  CubeEdgeTreeValidity T →
  RootedConnectedSkeleton (treeCodeGraph T) (root T) (vertices T)
validCodeRootedConnected validity = record
  { r-in-X = rootInVertices validity
  ; connected = connectedOnOwnEdges validity
  }

validCodeRootedPaths :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  (validity : CubeEdgeTreeValidity T) →
  RootedPathConnected (treeCodeGraph T) (root T) (vertices T)
validCodeRootedPaths validity =
  rootedConnectedSkeletonToRootedPathConnected
    (validCodeRootedConnected validity)

validCodeCompleteInsertionTree :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  (validity : CubeEdgeTreeValidity T) →
  CompleteInsertionParentTree
    {G = treeCodeGraph T}
    (root T)
    (vertices T)
validCodeCompleteInsertionTree {T = T} validity =
  pathUnionFoldToCompleteInsertionTree
    (validCodeRootedPaths validity)
    (treeCodeGraphSymmetry T)

edgePlusOneIsSuc : (m : ℕ) → m + 1 ≡ suc m
edgePlusOneIsSuc zero = refl
edgePlusOneIsSuc (suc m) = cong suc (edgePlusOneIsSuc m)

edgePlusOnePred : (m : ℕ) → (m + 1) ∸ 1 ≡ m
edgePlusOnePred m =
  trans (cong (λ k → k ∸ 1) (edgePlusOneIsSuc m)) refl

------------------------------------------------------------------------
-- Proof-free source-edge extraction from the reified insertion history.
--
-- An adjacency in `treeCodeGraph T` is itself a sigma witness whose first
-- component is an original `CubeGridEdgeCode`.  Keeping that component here
-- is important: later edge recovery can compare ordinary code lists, never
-- equality of the `forward`/`backward` proof fields inside `ParentLink`.

ownGraphAdjacencyEdge :
  ∀ {N} {T : CubeEdgeTreeCode N} {u v : CubeGridVertex4 N} →
  EdgeConnects (edges T) u v → CubeGridEdgeCode N
ownGraphAdjacencyEdge {T = T} (edge , edge∈ , endpoints) = edge

ownGraphAdjacencyEdgeInCode :
  ∀ {N} {T : CubeEdgeTreeCode N} {u v : CubeGridVertex4 N}
    (adjacency : EdgeConnects (edges T) u v) →
  ownGraphAdjacencyEdge {T = T} adjacency ∈ edges T
ownGraphAdjacencyEdgeInCode {T = T} (edge , edge∈ , endpoints) = edge∈

parentLinkSourceEdge :
  ∀ {N} {T : CubeEdgeTreeCode N} →
  ParentLink {G = treeCodeGraph T} (vertices T) → CubeGridEdgeCode N
parentLinkSourceEdge {T = T} link =
  ownGraphAdjacencyEdge {T = T} (PU.ParentLink.forward link)

parentLinkSourceEdgeInCode :
  ∀ {N} {T : CubeEdgeTreeCode N}
    (link : ParentLink {G = treeCodeGraph T} (vertices T)) →
  parentLinkSourceEdge {T = T} link ∈ edges T
parentLinkSourceEdgeInCode {T = T} link =
  ownGraphAdjacencyEdgeInCode {T = T} (PU.ParentLink.forward link)

-- The selected proof-free code has exactly the two possible orientations of
-- the corresponding insertion link.  This is the data bridge needed for the
-- later normalized-edge collision analysis; it erases the adjacency proof
-- while retaining both endpoint equalities.
parentLinkSourceEdgeEndpoints :
  ∀ {N} {T : CubeEdgeTreeCode N}
    (link : ParentLink {G = treeCodeGraph T} (vertices T)) →
  ((from (parentLinkSourceEdge {T = T} link) ≡ PU.ParentLink.parent link ×
    to   (parentLinkSourceEdge {T = T} link) ≡ PU.ParentLink.child link)
   ⊎
   (from (parentLinkSourceEdge {T = T} link) ≡ PU.ParentLink.child link ×
    to   (parentLinkSourceEdge {T = T} link) ≡ PU.ParentLink.parent link))
parentLinkSourceEdgeEndpoints {T = T} link =
  let source = PU.ParentLink.forward link
  in proj₂ (proj₂ source)

-- If two insertion links selected the same directed source code, their
-- endpoints either agree in the insertion orientation or are reversed.  This
-- is a finite four-case calculation over the two orientation witnesses; the
-- subsequent history argument rules out the reversed result.
sameSourceEdgeChildrenOrReversed :
  ∀ {N} {T : CubeEdgeTreeCode N}
    (left right : ParentLink {G = treeCodeGraph T} (vertices T)) →
  parentLinkSourceEdge {T = T} left ≡
  parentLinkSourceEdge {T = T} right →
  (PU.ParentLink.child left ≡ PU.ParentLink.child right)
  ⊎
  ((PU.ParentLink.parent left ≡ PU.ParentLink.child right) ×
   (PU.ParentLink.child left ≡ PU.ParentLink.parent right))
sameSourceEdgeChildrenOrReversed {T = T} left right sourceEq
  with parentLinkSourceEdgeEndpoints {T = T} left
     | parentLinkSourceEdgeEndpoints {T = T} right
     | gridEdgeCodeEqEndpoints sourceEq
... | inj₁ (leftFrom , leftTo) | inj₁ (rightFrom , rightTo)
    | sourceFrom , sourceTo =
  inj₁ (trans (sym leftTo) (trans sourceTo rightTo))
... | inj₁ (leftFrom , leftTo) | inj₂ (rightFrom , rightTo)
    | sourceFrom , sourceTo =
  inj₂
    ( trans (sym leftFrom) (trans sourceFrom rightFrom)
    , trans (sym leftTo) (trans sourceTo rightTo)
    )
... | inj₂ (leftFrom , leftTo) | inj₁ (rightFrom , rightTo)
    | sourceFrom , sourceTo =
  inj₂
    ( trans (sym leftTo) (trans sourceTo rightTo)
    , trans (sym leftFrom) (trans sourceFrom rightFrom)
    )
... | inj₂ (leftFrom , leftTo) | inj₂ (rightFrom , rightTo)
    | sourceFrom , sourceTo =
  inj₁ (trans (sym leftFrom) (trans sourceFrom rightFrom))

insertionSourceEdges :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  (validity : CubeEdgeTreeValidity T) → List (CubeGridEdgeCode N)
insertionSourceEdges {T = T} validity =
  mapList (parentLinkSourceEdge {T = T})
    (PU.CompleteInsertionParentTree.links
      (validCodeCompleteInsertionTree validity))

insertionSourceEdges⊆CodeEdges :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N}
    (validity : CubeEdgeTreeValidity T) →
  insertionSourceEdges validity ⊆ edges T
insertionSourceEdges⊆CodeEdges {T = T} validity edge∈ =
  let source =
        map-elem (parentLinkSourceEdge {T = T})
          (PU.CompleteInsertionParentTree.links
            (validCodeCompleteInsertionTree validity))
          edge∈
      edge≡selected = proj₁ (proj₂ source)
  in subst
       (λ edge → edge ∈ edges T)
       (sym edge≡selected)
       (parentLinkSourceEdgeInCode {T = T} (proj₁ source))

-- The insertion history has one selected parent edge for every non-root
-- carrier vertex.  Since the source code is numerically a tree, this is
-- exactly its edge count.  This result deliberately says nothing yet about
-- duplicate selected edges; the next edge-collapse lemma will combine this
-- equality with the source's unoriented no-duplicate invariant.
insertionSourceEdgesLength :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  (validity : CubeEdgeTreeValidity T) →
  length (insertionSourceEdges validity) ≡ edgeCount T
insertionSourceEdgesLength {T = T} validity =
  trans
    (listMapLength (parentLinkSourceEdge {T = T})
      (PU.CompleteInsertionParentTree.links complete))
    (trans
      (linksLength (PU.CompleteInsertionParentTree.history complete))
      (trans
        (cong (λ m → m ∸ 1) includedLength)
        (trans
          (cong (λ m → m ∸ 1) (vertexEdgeCount validity))
          (edgePlusOnePred (edgeCount T)))))
  where
  complete : CompleteInsertionParentTree
    {G = treeCodeGraph T} (root T) (vertices T)
  complete = validCodeCompleteInsertionTree validity

  includedLength :
    length (PU.CompleteInsertionParentTree.included complete)
      ≡ length (vertices T)
  includedLength =
    GC.sameVertexSetNoDuplicatesLength
      (PU.CompleteInsertionParentTree.includedNoDuplicates complete)
      (verticesNoDuplicates validity)
      (PU.CompleteInsertionParentTree.rangeExact complete)

-- The selected source edges carry pairwise distinct insertion children.
-- This is a property of the insertion history itself, not of the source edge
-- presentation.  The following normalized-edge collapse only has to show
-- that a collision of geometric edge codes would force such a child
-- collision (the reversed-orientation case is excluded by insertion order).
insertionSourceEdgeChildrenNoDuplicates :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  (validity : CubeEdgeTreeValidity T) →
  NoDuplicates
    (mapList PU.ParentLink.child
      (PU.CompleteInsertionParentTree.links
        (validCodeCompleteInsertionTree validity)))
insertionSourceEdgeChildrenNoDuplicates validity =
  insertionChildrenNoDuplicates
    (PU.CompleteInsertionParentTree.history
      (validCodeCompleteInsertionTree validity))

-- The reversed orientation of a common source edge would give both
-- `child₂ < parent₂` and `parent₂ < child₂` in the duplicate-free insertion
-- carrier.  Hence a raw source-code collision already forces equality of
-- insertion children.
sameInsertionSourceEdgeChildren :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N}
    (validity : CubeEdgeTreeValidity T)
    {left right : ParentLink {G = treeCodeGraph T} (vertices T)} →
  left ∈ PU.CompleteInsertionParentTree.links
    (validCodeCompleteInsertionTree validity) →
  right ∈ PU.CompleteInsertionParentTree.links
    (validCodeCompleteInsertionTree validity) →
  parentLinkSourceEdge {T = T} left ≡
  parentLinkSourceEdge {T = T} right →
  PU.ParentLink.child left ≡ PU.ParentLink.child right
sameInsertionSourceEdgeChildren {T = T} validity {left} {right}
  left∈ right∈ sourceEq
  with sameSourceEdgeChildrenOrReversed {T = T} left right sourceEq
... | inj₁ sameChild = sameChild
... | inj₂ (leftParent≡rightChild , leftChild≡rightParent) =
  ⊥-elim
    (appearsBeforeAsymmetric includedNoDup reversedBefore rightBefore)
  where
  complete : CompleteInsertionParentTree
    {G = treeCodeGraph T} (root T) (vertices T)
  complete = validCodeCompleteInsertionTree validity

  history = PU.CompleteInsertionParentTree.history complete
  includedNoDup = PU.CompleteInsertionParentTree.includedNoDuplicates complete

  leftBefore : AppearsBefore
    (PU.ParentLink.parent left) (PU.ParentLink.child left)
    (PU.CompleteInsertionParentTree.included complete)
  leftBefore = historyParentBeforeChild history left∈

  rightBefore : AppearsBefore
    (PU.ParentLink.parent right) (PU.ParentLink.child right)
    (PU.CompleteInsertionParentTree.included complete)
  rightBefore = historyParentBeforeChild history right∈

  reversedBefore : AppearsBefore
    (PU.ParentLink.child right) (PU.ParentLink.parent right)
    (PU.CompleteInsertionParentTree.included complete)
  reversedBefore =
    subst
      (λ z → AppearsBefore (PU.ParentLink.child right) z
        (PU.CompleteInsertionParentTree.included complete))
      leftChild≡rightParent
      (subst
        (λ z → AppearsBefore z (PU.ParentLink.child left)
          (PU.CompleteInsertionParentTree.included complete))
        leftParent≡rightChild
        leftBefore)

insertionSourceEdgesNoDuplicates :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  (validity : CubeEdgeTreeValidity T) →
  NoDuplicates (insertionSourceEdges validity)
insertionSourceEdgesNoDuplicates {T = T} validity =
  mapList-noDup-by-projection
    (parentLinkSourceEdge {T = T}) PU.ParentLink.child links
    (λ left∈ right∈ sourceEq →
      sameInsertionSourceEdgeChildren validity left∈ right∈ sourceEq)
    (insertionSourceEdgeChildrenNoDuplicates validity)
  where
  links = PU.CompleteInsertionParentTree.links
    (validCodeCompleteInsertionTree validity)

-- The numerical tree invariant now collapses the selected source-edge list
-- onto the entire proof-free edge carrier extensionally.  This is the exact
-- finite-cardinality step: no tree-edge presentation is lost by the
-- path-union reification.
insertionSourceEdgesSameMembersAsCode :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  (validity : CubeEdgeTreeValidity T) →
  SameVertexSet (insertionSourceEdges validity) (edges T)
insertionSourceEdgesSameMembersAsCode {T = T} validity =
  noDupSubsetEqualLengthSameVertexSet cubeGridEdgeCodeEq?
    (insertionSourceEdgesNoDuplicates validity)
    (edgesNoDuplicates validity)
    (insertionSourceEdges⊆CodeEdges validity)
    (insertionSourceEdgesLength validity)

mapListSameVertexSet :
  ∀ {A B} (f : A → B) {xs ys : List A} →
  SameVertexSet xs ys → SameVertexSet (mapList f xs) (mapList f ys)
mapListSameVertexSet f {xs = xs} {ys = ys} (xs⊆ys , ys⊆xs) =
  mapForward , mapBackward
  where
  mapForward : mapList f xs ⊆ mapList f ys
  mapForward {z} z∈mapped =
    let source = map-elem f xs z∈mapped
        x = proj₁ source
        z≡fx = proj₁ (proj₂ source)
        x∈xs = proj₂ (proj₂ source)
    in subst (λ w → w ∈ mapList f ys) (sym z≡fx)
         (in-map f (xs⊆ys x∈xs))

  mapBackward : mapList f ys ⊆ mapList f xs
  mapBackward {z} z∈mapped =
    let source = map-elem f ys z∈mapped
        y = proj₁ source
        z≡fy = proj₁ (proj₂ source)
        y∈ys = proj₂ (proj₂ source)
    in subst (λ w → w ∈ mapList f xs) (sym z≡fy)
         (in-map f (ys⊆xs y∈ys))

canonicalizeSameVertexSet :
  ∀ {G : GC.Graph} {xs ys : List (GC.Graph.Vertex G)} →
  SameVertexSet xs ys →
  SameVertexSet (canonicalize {G = G} xs) (canonicalize {G = G} ys)
canonicalizeSameVertexSet {G = G} {xs = xs} {ys = ys} (xs⊆ys , ys⊆xs) =
  forward , backward
  where
  forward : canonicalize {G = G} xs ⊆ canonicalize {G = G} ys
  forward {x} x∈canonical =
    canonicalizeComplete {G = G}
      (xs⊆ys (canonicalizeSound {G = G} x∈canonical))

  backward : canonicalize {G = G} ys ⊆ canonicalize {G = G} xs
  backward {y} y∈canonical =
    canonicalizeComplete {G = G}
      (ys⊆xs (canonicalizeSound {G = G} y∈canonical))

insertionCanonicalEdges :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  CubeEdgeTreeValidity T → List (CubeGridEdgeCode N)
insertionCanonicalEdges {N} {T} validity =
  canonicalize {G = edgeCodeGraph {N}}
    (mapList normaliseGridEdge (insertionSourceEdges validity))

-- Canonicalization turns the extensional raw-edge collapse into literal list
-- equality.  This is the proof-free edge-recovery target consumed by the DFS
-- tour decoder.
insertionCanonicalEdges≡canonicalEdges :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  (validity : CubeEdgeTreeValidity T) →
  insertionCanonicalEdges validity ≡ canonicalEdges T
insertionCanonicalEdges≡canonicalEdges {N} {T} validity =
  GC.SameVertexSetCanonicalListEq.sameVertexSetCanonicalListEq
    (GC.vertexOrderIsTotalOrder {G = edgeCodeGraph {N}})
    insertionCanonical
    sourceCanonical
    normalisedSameMembers
  where
  normalisedSameMembers :
    SameVertexSet
      (insertionCanonicalEdges validity)
      (canonicalEdges T)
  normalisedSameMembers = canonicalizeSameVertexSet
    (mapListSameVertexSet normaliseGridEdge
      (insertionSourceEdgesSameMembersAsCode validity))

  insertionCanonical : CanonicalVertexList
    (GC.vertexOrder {G = edgeCodeGraph {N}})
    (insertionCanonicalEdges validity)
  insertionCanonical = record
    { noDup = canonicalizeNoDup {G = edgeCodeGraph {N}}
        (mapList normaliseGridEdge (insertionSourceEdges validity))
    ; sorted = canonicalizeSorted {G = edgeCodeGraph {N}}
        (mapList normaliseGridEdge (insertionSourceEdges validity))
    }

  sourceCanonical : CanonicalVertexList
    (GC.vertexOrder {G = edgeCodeGraph {N}})
    (canonicalEdges T)
  sourceCanonical = record
    { noDup = canonicalEdges-noDuplicates T
    ; sorted = canonicalizeSorted {G = edgeCodeGraph {N}}
        (mapList normaliseGridEdge (edges T))
    }

adjacentPairUsesOwnGraphEdge :
  ∀ {N} {T : CubeEdgeTreeCode N} {vs : List (CubeGridVertex4 N)} →
  ConsecutiveEdges (treeCodeGraph T) vs →
  {e : CubeGridEdgeCode N} → e ∈ adjacentPairs vs →
  EdgeConnects (edges T) (from e) (to e)
adjacentPairUsesOwnGraphEdge {T = T} (GC.edges-single {x = x}) ()
adjacentPairUsesOwnGraphEdge
  {T = T} (GC.edges-step {x = u} {y = v} {xs = vs} adjacency remaining) {e = e} GC.here =
  adjacency
adjacentPairUsesOwnGraphEdge
  {T = T} (GC.edges-step {x = u} {y = v} {xs = vs} adjacency remaining)
  {e = e} (GC.there pair∈) =
  adjacentPairUsesOwnGraphEdge {T = T} {vs = v ∷ vs}
    remaining {e = e} pair∈

adjacentPairNormalisedInCode :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N}
    (validity : CubeEdgeTreeValidity T)
    {pair : CubeGridEdgeCode N} →
  EdgeConnects (edges T) (from pair) (to pair) →
  normaliseGridEdge pair ∈ canonicalEdges T
adjacentPairNormalisedInCode {T = T} validity {pair}
  (source , source∈ , inj₁ (sourceFrom , sourceTo)) =
  subst (λ z → z ∈ canonicalEdges T) (sym normalisedEq)
    (canonicalEdges-complete {T = T} source source∈)
  where
  sourceEqPair : source ≡ pair
  sourceEqPair = gridEdgeCodeExt sourceFrom sourceTo

  normalisedEq : normaliseGridEdge pair ≡ normaliseGridEdge source
  normalisedEq = cong normaliseGridEdge (sym sourceEqPair)
adjacentPairNormalisedInCode {T = T} validity {pair}
  (source , source∈ , inj₂ (sourceFrom , sourceTo)) =
  subst (λ z → z ∈ canonicalEdges T) (sym normalisedEq)
    (canonicalEdges-complete {T = T} source source∈)
  where
  sourceEqReversePair : source ≡ reverseGridEdge pair
  sourceEqReversePair = gridEdgeCodeExt sourceFrom sourceTo

  pairAdmissible : GridEdgeAdmissible pair
  pairAdmissible = treeCodeAdjacencyIsFaceAdj validity
    (source , source∈ , inj₂ (sourceFrom , sourceTo))

  normalisedEq : normaliseGridEdge pair ≡ normaliseGridEdge source
  normalisedEq =
    trans (normaliseGridEdge-reverse pair pairAdmissible)
      (cong normaliseGridEdge (sym sourceEqReversePair))

-- The tour cannot manufacture a cube-grid edge: every recovered adjacent
-- pair is an own-edge adjacency of the original proof-free code.  The
-- converse coverage direction is the remaining structural edge theorem.
cubeEdgeTourCanonicalEdges⊆CodeEdges :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  (validity : CubeEdgeTreeValidity T) →
  {tour : List (CubeGridVertex4 N)} →
  ConsecutiveEdges (treeCodeGraph T) tour →
  tourCanonicalEdges tour ⊆ canonicalEdges T
cubeEdgeTourCanonicalEdges⊆CodeEdges {N = N} {T = T} validity {tour = tour}
  tourAdjacent {e} e∈tour =
  let e∈mapped = canonicalizeSound {G = edgeCodeGraph {N}}
        {xs = mapList normaliseGridEdge
          (adjacentPairs tour)} e∈tour
      source = map-elem normaliseGridEdge
        (adjacentPairs tour) e∈mapped
      pair = proj₁ source
      e≡normalised = proj₁ (proj₂ source)
      pair∈ = proj₂ (proj₂ source)
      ownAdj = adjacentPairUsesOwnGraphEdge {T = T} {vs = tour}
        tourAdjacent {e = pair} pair∈
  in subst (λ z → z ∈ canonicalEdges T) (sym e≡normalised)
       (adjacentPairNormalisedInCode validity ownAdj)

validCodeToConstructiveRootedSpanningTree :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  (validity : CubeEdgeTreeValidity T) →
  ConstructiveRootedSpanningTree
    (treeCodeGraph T)
    (root T)
    (vertices T)
validCodeToConstructiveRootedSpanningTree validity =
  completeInsertionTreeToConstructiveRootedSpanningTree
    (validCodeCompleteInsertionTree validity)
    (verticesNoDuplicates validity)

validCodeToRootedTreeNode :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  (validity : CubeEdgeTreeValidity T) →
  RootedTreeNode (treeCodeGraph T) (root T)
validCodeToRootedTreeNode validity =
  ConstructiveRootedSpanningTree.tree
    (validCodeToConstructiveRootedSpanningTree validity)

cubeEdgeDFSTour :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  (validity : CubeEdgeTreeValidity T) →
  List (GC.Graph.Vertex (treeCodeGraph T))
cubeEdgeDFSTour validity = dfsTour (validCodeToRootedTreeNode validity)

cubeEdgeDFSTourInvariant :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  (validity : CubeEdgeTreeValidity T) →
  DFSTourInvariant (validCodeToRootedTreeNode validity)
cubeEdgeDFSTourInvariant validity =
  dfsTourInvariant (validCodeToRootedTreeNode validity)

cubeEdgeDFSTourCanonicalEdges⊆CodeEdges :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  (validity : CubeEdgeTreeValidity T) →
  tourCanonicalEdges (cubeEdgeDFSTour validity) ⊆ canonicalEdges T
cubeEdgeDFSTourCanonicalEdges⊆CodeEdges validity =
  cubeEdgeTourCanonicalEdges⊆CodeEdges validity
    (DFSTourInvariant.adjacent (cubeEdgeDFSTourInvariant validity))

-- This is the vertex half of the lossless-tour interface.  It is already
-- exact: the structural tour covers the reified tree, and reification covers
-- precisely the code's vertex carrier.  The remaining edge half must show
-- that the path-union tree has retained every source edge; that is where the
-- cardinality-collapse argument belongs.
cubeEdgeDFSTourRange :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  (validity : CubeEdgeTreeValidity T) →
  SameVertexSet (cubeEdgeDFSTour validity) (vertices T)
cubeEdgeDFSTourRange validity =
  sameVertexSet-trans
    (DFSTourInvariant.rangeExact (cubeEdgeDFSTourInvariant validity))
    (CDFS.constructiveTreeRangeIs
      (validCodeToConstructiveRootedSpanningTree validity))

-- Canonicalising the closed tour recovers the literal canonical source
-- vertex list, rather than merely an extensionally equal carrier.  This is
-- the first half of the eventual proof-free DFS decoder.
cubeEdgeDFSTourRecoversCanonicalVertices :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  (validity : CubeEdgeTreeValidity T) →
  tourCanonicalVertices (cubeEdgeDFSTour validity) ≡ canonicalVertices T
cubeEdgeDFSTourRecoversCanonicalVertices {N} {T} validity =
  Canonical.sameVertexSetCanonicalListEq
    (record
      { noDup = tourCanonicalVertices-noDuplicates (cubeEdgeDFSTour validity)
      ; sorted = canonicalizeSorted {G = faceCubeGraph {N}}
          (cubeEdgeDFSTour validity)
      })
    (record
      { noDup = canonicalVertices-noDuplicates T
      ; sorted = canonicalizeSorted {G = faceCubeGraph {N}} (vertices T)
      })
    sameMembers
  where
  module Canonical = GC.SameVertexSetCanonicalListEq
    (GC.vertexOrderIsTotalOrder {G = faceCubeGraph {N}})

  tour⊆code :
    tourCanonicalVertices (cubeEdgeDFSTour validity) ⊆ canonicalVertices T
  tour⊆code x∈tour =
    canonicalizeComplete {G = faceCubeGraph {N}}
      (proj₁ (cubeEdgeDFSTourRange validity)
        (canonicalizeSound {G = faceCubeGraph {N}} x∈tour))

  code⊆tour :
    canonicalVertices T ⊆ tourCanonicalVertices (cubeEdgeDFSTour validity)
  code⊆tour x∈code =
    canonicalizeComplete {G = faceCubeGraph {N}}
      (proj₂ (cubeEdgeDFSTourRange validity)
        (canonicalizeSound {G = faceCubeGraph {N}} x∈code))

  sameMembers :
    SameVertexSet
      (tourCanonicalVertices (cubeEdgeDFSTour validity))
      (canonicalVertices T)
  sameMembers = tour⊆code , code⊆tour

cubeEdgeDFSTourLengthByCodeVertices :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  (validity : CubeEdgeTreeValidity T) →
  length (cubeEdgeDFSTour validity) ∸ 1 ≡
    (length (vertices T) ∸ 1) + (length (vertices T) ∸ 1)
cubeEdgeDFSTourLengthByCodeVertices {T = T} validity =
  let spanning = validCodeToConstructiveRootedSpanningTree validity
      flattenLength :
        length (CDFS.flattenTree (CDFS.ConstructiveRootedSpanningTree.tree spanning))
          ≡ length (vertices T)
      flattenLength =
        trans
          (cong length (sym (CDFS.ConstructiveRootedSpanningTree.flattenCorrect spanning)))
          (CDFS.ConstructiveRootedSpanningTree.flattenSize spanning)
  in subst
       (λ m →
         length (cubeEdgeDFSTour validity) ∸ 1 ≡
         (m ∸ 1) + (m ∸ 1))
       flattenLength
       (DFSTourInvariant.lengthExact (cubeEdgeDFSTourInvariant validity))

-- The closed tour has exactly two code-edge moves per source edge.  This is
-- the numerical half of the later edge-collapse argument; it follows before
-- identifying which individual code edges the path-union tree selected.
cubeEdgeDFSTourLengthByCodeEdges :
  ∀ {N} {{_ : NonZero N}} {T : CubeEdgeTreeCode N} →
  (validity : CubeEdgeTreeValidity T) →
  length (cubeEdgeDFSTour validity) ∸ 1 ≡
    edgeCount T + edgeCount T
cubeEdgeDFSTourLengthByCodeEdges {T = T} validity =
  trans
    (cubeEdgeDFSTourLengthByCodeVertices validity)
    (trans
      (cong
        (λ m → (m ∸ 1) + (m ∸ 1))
        (vertexEdgeCount validity))
      (cong₂ _+_
        (edgePlusOnePred (edgeCount T))
        (edgePlusOnePred (edgeCount T))))
