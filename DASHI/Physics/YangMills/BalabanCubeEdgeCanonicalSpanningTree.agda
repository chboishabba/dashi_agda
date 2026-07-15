module DASHI.Physics.YangMills.BalabanCubeEdgeCanonicalSpanningTree where

------------------------------------------------------------------------
-- Constructive spanning-tree view of a valid CMP 109 cube-edge code.
--
-- The ambient graph here is deliberately `treeCodeGraph T`, not the
-- induced face-cube graph on its vertices.  Consequently every edge used by
-- the path-union construction is an edge already present in the proof-free
-- source code; no geometric chord can be introduced at this boundary.
------------------------------------------------------------------------

open import Data.Nat.Base using (NonZero)
open import Data.List.Base using (List)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC using
  ( _∈_
  ; RootedConnectedSkeleton
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
        )
open import DASHI.Physics.YangMills.P06PathUnionSpanningTreeClosure as PU
  using ( CompleteInsertionParentTree
        ; pathUnionFoldToCompleteInsertionTree
        ; completeInsertionTreeToConstructiveRootedSpanningTree
        )
open import DASHI.Physics.YangMills.BalabanCubeEdgeTreeCodes public

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
  dfsTourInvariant
    (validCodeToRootedTreeNode validity)
    (ConstructiveRootedSpanningTree.noDuplicateVertices
      (validCodeToConstructiveRootedSpanningTree validity))
