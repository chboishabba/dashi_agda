module DASHI.Physics.YangMills.P06BidirectionalSpanningTreeClosure where

------------------------------------------------------------------------
-- P06-local bidirectional spanning-tree closure.
--
-- This module deliberately leaves `Graph` directed.  The input attached to
-- each canonical skeleton supplies reverse adjacency only on that carrier,
-- together with the finite shortest-path/parent-tree construction needed to
-- build its eliminable spanning tree.  The output is the exact-length DFS
-- map used by the P06 count injection.
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)

open import DASHI.Physics.YangMills.GraphCombinatorics as GC
  using ( Graph
        ; BoundedNeighbourEnumeration
        ; CanonicalSkeletonEnumeration
        ; CanonicalSkeletonObject
        ; CountWalksMembershipSemantics
        ; countSkeletons
        )

open import DASHI.Physics.YangMills.P06ConstructiveSpanningTreeDFS as CDFS
  using ( p06DFSWalkLength
        ; BidirectionalCanonicalDFSInput
        ; UndirectedGraphStructure
        ; SkeletonAdjacencySymmetry
        ; undirectedGraphGivesSkeletonSymmetry
        ; RootedPathConnected
        ; rootedConnectedSkeletonToRootedPathConnected
        ; RootedShortestPathSelector
        ; RankedBidirectionalParentTree
        ; ShortestPathParentConstruction
        )

open import DASHI.Physics.YangMills.P06DFSValidWalkSurface as Surface
  using ( GeneratedWalkSemanticsCompatibility
        ; DFSValidWalkMapWitnessAtLength
        ; canonicalSkeletonEnumerationToOwnedDFSValidWalkMapAtLength
        )

------------------------------------------------------------------------
-- Per-enumeration closure data.  `dfsMap` is a theorem-backed projection;
-- there is no opaque legacy TreeDFSWalk and no total index on arbitrary
-- vertex lists.
------------------------------------------------------------------------

record P06BidirectionalSpanningTreeClosure
  {G : Graph} {Δ : ℕ} {r : Graph.Vertex G} {n : ℕ}
  (CE : CanonicalSkeletonEnumeration G r n)
  (BNE : BoundedNeighbourEnumeration G Δ)
  (WE : CountWalksMembershipSemantics G r (p06DFSWalkLength n)) : Set₁ where
  field
    semanticsCompatibility : GeneratedWalkSemanticsCompatibility BNE WE
    dfsInput :
      (s : Fin (countSkeletons G r n)) →
      BidirectionalCanonicalDFSInput
        (CanonicalSkeletonEnumeration.objectOf CE s)

  dfsMap : DFSValidWalkMapWitnessAtLength CE BNE WE
  dfsMap = canonicalSkeletonEnumerationToOwnedDFSValidWalkMapAtLength
    CE BNE WE semanticsCompatibility dfsInput

------------------------------------------------------------------------
-- A globally undirected polymer graph discharges the local symmetry part;
-- finite shortest-path selection and parent-tree recursion remain separate
-- constructive obligations, as they should.
------------------------------------------------------------------------

undirectedClosureLocalSymmetry :
  {G : Graph} {X : List (Graph.Vertex G)} →
  UndirectedGraphStructure G →
  SkeletonAdjacencySymmetry X
undirectedClosureLocalSymmetry = undirectedGraphGivesSkeletonSymmetry
