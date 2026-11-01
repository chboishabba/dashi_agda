module DASHI.Physics.YangMills.BalabanP06OwnedGraphCombinatoricsExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Reinhard Diestel, "Graph Theory", Graduate Texts in Mathematics 173,
-- 5th edition, Springer, 2017. DOI: 10.1007/978-3-662-53622-3.
--
-- This module does not import a new graph-theory axiom.  It packages the
-- term-level P06 graph consequences already proved in GraphCombinatorics so
-- the submission cutset can distinguish genuinely owned combinatorics from
-- the remaining source-side polymer model and diameter-complexity leaves.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ)
open import Data.List.Base using (List; length)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _*_; _∸_; _^_)
open import DASHI.Core.Prelude using (_×_)

import DASHI.Physics.YangMills.GraphCombinatorics as Graph
open import DASHI.Physics.YangMills.CompactLieProofLevel

record OwnedP06GraphCombinatorics : Set₁ where
  field
    rootedConnectedSkeletonHasRootedSpanningTree :
      {G : Graph.Graph}
      {root : Graph.Graph.Vertex G}
      {vertices : List (Graph.Graph.Vertex G)} →
      Graph.RootedConnectedSkeleton G root vertices →
      Σ (Graph.SpanningTree G vertices) (λ spanningTree →
        Σ (Graph.Graph.Vertex (Graph.SpanningTree.T spanningTree)) (λ treeRoot →
          (Graph.SpanningTree.embed spanningTree treeRoot ≡ root)
          × Graph.RootedTree (Graph.SpanningTree.T spanningTree) treeRoot))

    rootedTreeHasControlledDFSWalk :
      {T : Graph.Graph}
      {root : Graph.Graph.Vertex T} →
      (vertexCount : ℕ) →
      Graph.RootedTree T root →
      Graph.Tree T →
      Graph.countVertices T ≡ vertexCount →
      Σ (Graph.TreeDFSWalk T root) (λ walk →
        Graph.TreeDFSWalk.length-w walk ≡
          2 * (vertexCount ∸ 1))

    boundedDegreeRootedWalkCount :
      {G : Graph.Graph}
      {degreeBound : ℕ} →
      Graph.BoundedDegree G degreeBound →
      (root : Graph.Graph.Vertex G) →
      (walkLength : ℕ) →
      Graph.countWalks G root walkLength ≤ degreeBound ^ walkLength

    connectedSkeletonCoveredByControlledDFS :
      {G : Graph.Graph}
      {root : Graph.Graph.Vertex G}
      {vertices : List (Graph.Graph.Vertex G)} →
      (vertexCount : ℕ) →
      Graph.RootedConnectedSkeleton G root vertices →
      length vertices ≡ vertexCount →
      Graph.DFSCover G root vertices vertexCount

    visitedSetCardinalityBound :
      {G : Graph.Graph} →
      (walk : List (Graph.Graph.Vertex G)) →
      (walkLength : ℕ) →
      length walk ≡ walkLength →
      Graph.countUnique walk ≤ suc walkLength

open OwnedP06GraphCombinatorics public

currentOwnedP06GraphCombinatorics : OwnedP06GraphCombinatorics
currentOwnedP06GraphCombinatorics = record
  { rootedConnectedSkeletonHasRootedSpanningTree =
      Graph.P06a2bConnectedSkeletonHasRootedSpanningTree
  ; rootedTreeHasControlledDFSWalk =
      Graph.P06a2cRootedTreeDFSWalk
  ; boundedDegreeRootedWalkCount =
      Graph.P06a2dBoundedDegreeWalkCount
  ; connectedSkeletonCoveredByControlledDFS =
      Graph.P06a2eConnectedSkeletonCoveredByDFSWalk
  ; visitedSetCardinalityBound =
      Graph.WalkVisitedSetSizeBound
  }

ownedP06GraphCombinatoricsLevel : ProofLevel
ownedP06GraphCombinatoricsLevel = machineChecked
