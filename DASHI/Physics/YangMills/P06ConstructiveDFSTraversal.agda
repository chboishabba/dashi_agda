module DASHI.Physics.YangMills.P06ConstructiveDFSTraversal where

------------------------------------------------------------------------
-- P06 constructive DFS traversal surface.
--
-- The legacy TreeDFSWalk records coverage/length metadata only.  This
-- surface records the geometric path invariant at the point where a
-- traversal is supplied.  Its length is deliberately bounded: a closed DFS
-- tour of an n-vertex tree has 2(n - 1) edges, not definitionally n + n.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List; length)
open import Data.Nat.Base using (ℕ; _+_; _∸_; _≤_)
open import Data.Product using (Σ; _,_)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC
  using ( Graph
        ; NonEmpty
        ; head
        ; last
        ; ConsecutiveEdges
        ; Path
        ; pathLength
        ; SameVertexSet
        ; _⊆_
        ; CanonicalSkeletonObject
        )

------------------------------------------------------------------------
-- A traversal whose path facts have not been erased.
------------------------------------------------------------------------

record ValidTreeDFSWalk
  (G : Graph)
  (r : Graph.Vertex G)
  (X : List (Graph.Vertex G)) : Set₁ where
  field
    walkVertices : List (Graph.Vertex G)
    nonEmpty : NonEmpty walkVertices
    startsAt : head walkVertices nonEmpty ≡ r
    endpoint : Graph.Vertex G
    endsAt : last walkVertices nonEmpty ≡ endpoint
    adjacent : ConsecutiveEdges G walkVertices
    visitsAll : X ⊆ walkVertices
    visitsOnly : walkVertices ⊆ X
    lengthBound : pathLength
      (record
        { vertices = walkVertices
        ; nonEmptyWitness = nonEmpty
        ; startsAt = startsAt
        ; endsAt = endsAt
        ; adjacent = adjacent
        }) ≤ length X + length X

validTreeDFSWalkRangeIs :
  {G : Graph} {r : Graph.Vertex G} {X : List (Graph.Vertex G)} →
  (w : ValidTreeDFSWalk G r X) →
  SameVertexSet X (ValidTreeDFSWalk.walkVertices w)
validTreeDFSWalkRangeIs w =
  ValidTreeDFSWalk.visitsAll w , ValidTreeDFSWalk.visitsOnly w

validTreeDFSWalkToPath :
  {G : Graph} {r : Graph.Vertex G} {X : List (Graph.Vertex G)} →
  (w : ValidTreeDFSWalk G r X) →
  Path G r (ValidTreeDFSWalk.endpoint w)
validTreeDFSWalkToPath w = record
  { vertices = ValidTreeDFSWalk.walkVertices w
  ; nonEmptyWitness = ValidTreeDFSWalk.nonEmpty w
  ; startsAt = ValidTreeDFSWalk.startsAt w
  ; endsAt = ValidTreeDFSWalk.endsAt w
  ; adjacent = ValidTreeDFSWalk.adjacent w
  }

------------------------------------------------------------------------
-- Canonical-skeleton specialization.
------------------------------------------------------------------------

record RootedTreeDFSPath
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  (obj : CanonicalSkeletonObject G r n) : Set₁ where
  field
    vertices : List (Graph.Vertex G)
    nonEmpty : NonEmpty vertices
    startsAt : head vertices nonEmpty ≡ r
    endpoint : Graph.Vertex G
    endsAt : last vertices nonEmpty ≡ endpoint
    adjacent : ConsecutiveEdges G vertices
    coversSkeleton :
      CanonicalSkeletonObject.skelVertices obj ⊆ vertices
    staysInSkeleton :
      vertices ⊆ CanonicalSkeletonObject.skelVertices obj
    lengthBound :
      pathLength
        (record
          { vertices = vertices
          ; nonEmptyWitness = nonEmpty
          ; startsAt = startsAt
          ; endsAt = endsAt
          ; adjacent = adjacent
          }) ≤ n + n

rootedTreeDFSPathRangeIs :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {obj : CanonicalSkeletonObject G r n} →
  (w : RootedTreeDFSPath obj) →
  SameVertexSet
    (RootedTreeDFSPath.vertices w)
    (CanonicalSkeletonObject.skelVertices obj)
rootedTreeDFSPathRangeIs w =
  RootedTreeDFSPath.staysInSkeleton w ,
  RootedTreeDFSPath.coversSkeleton w

------------------------------------------------------------------------
-- The actual constructive input.  This is intentionally a record rather
-- than a postulate: an implementation must supply adjacency, root/end facts,
-- coverage, containment, and the length bound together.
------------------------------------------------------------------------

record ConstructiveRootedTreeDFS
  {G : Graph} {r : Graph.Vertex G} {n : ℕ} : Set₁ where
  field
    traverse :
      (obj : CanonicalSkeletonObject G r n) →
      RootedTreeDFSPath obj

constructiveRootedTreeDFS :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ} →
  ConstructiveRootedTreeDFS {G = G} {r = r} {n = n} →
  (obj : CanonicalSkeletonObject G r n) →
  RootedTreeDFSPath obj
constructiveRootedTreeDFS = ConstructiveRootedTreeDFS.traverse

validTreeDFSWalkFromRootedTreeDFSPath :
  {G : Graph} {r : Graph.Vertex G} {n : ℕ}
  {obj : CanonicalSkeletonObject G r n} →
  RootedTreeDFSPath obj →
  ValidTreeDFSWalk G r
    (CanonicalSkeletonObject.skelVertices obj)
validTreeDFSWalkFromRootedTreeDFSPath w = record
  { walkVertices = RootedTreeDFSPath.vertices w
  ; nonEmpty = RootedTreeDFSPath.nonEmpty w
  ; startsAt = RootedTreeDFSPath.startsAt w
  ; endpoint = RootedTreeDFSPath.endpoint w
  ; endsAt = RootedTreeDFSPath.endsAt w
  ; adjacent = RootedTreeDFSPath.adjacent w
  ; visitsAll = RootedTreeDFSPath.coversSkeleton w
  ; visitsOnly = RootedTreeDFSPath.staysInSkeleton w
  ; lengthBound =
      substLengthBound
        (CanonicalSkeletonObject.size obj)
        (RootedTreeDFSPath.lengthBound w)
  }
  where
  substLengthBound :
    {G : Graph} {r : Graph.Vertex G} {n : ℕ}
    {obj : CanonicalSkeletonObject G r n} →
    length (CanonicalSkeletonObject.skelVertices obj) ≡ n →
    pathLength
      (record
        { vertices = RootedTreeDFSPath.vertices w
        ; nonEmptyWitness = RootedTreeDFSPath.nonEmpty w
        ; startsAt = RootedTreeDFSPath.startsAt w
        ; endsAt = RootedTreeDFSPath.endsAt w
        ; adjacent = RootedTreeDFSPath.adjacent w
        })
      ≤ length (CanonicalSkeletonObject.skelVertices obj)
        + length (CanonicalSkeletonObject.skelVertices obj) →
    pathLength
      (record
        { vertices = RootedTreeDFSPath.vertices w
        ; nonEmptyWitness = RootedTreeDFSPath.nonEmpty w
        ; startsAt = RootedTreeDFSPath.startsAt w
        ; endsAt = RootedTreeDFSPath.endsAt w
        ; adjacent = RootedTreeDFSPath.adjacent w }) ≤ n + n
  substLengthBound refl bound = bound

