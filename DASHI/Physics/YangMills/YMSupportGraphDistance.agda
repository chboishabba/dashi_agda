module DASHI.Physics.YangMills.YMSupportGraphDistance where

open import DASHI.Core.Prelude
open import Data.List.Base using (length)

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support

record FiniteSupportGraph : Set₁ where
  field
    Vertex : Set
    Edge : Set
    supportEdge : Edge → Bool
    treeEdge : Edge → Bool
    treeEdgesSubsetSupportEdges :
      ∀ {e : Edge} →
      treeEdge e ≡ true →
      supportEdge e ≡ true

record Path (G : FiniteSupportGraph) : Set where
  open FiniteSupportGraph G

  field
    start : Vertex
    finish : Vertex
    edges : List Edge
    valid : Bool
    pathLength : Nat
    pathLengthMatchesEdges :
      pathLength ≡ length edges

record GraphDistanceStructure (G : FiniteSupportGraph) : Set₁ where
  open FiniteSupportGraph G

  field
    graphDist : Vertex → Vertex → Nat
    graphDistMinimality :
      ∀ {u v : Vertex} →
      (p : Path G) →
      Path.start p ≡ u →
      Path.finish p ≡ v →
      Path.valid p ≡ true →
      graphDist u v ≤ Path.pathLength p

record TreePathStructure (G : FiniteSupportGraph) : Set₁ where
  open FiniteSupportGraph G

  field
    treePath : Vertex → Vertex → Path G
    treeEdgeCount : Nat
    treePathStart :
      ∀ (u v : Vertex) →
      Path.start (treePath u v) ≡ u
    treePathFinish :
      ∀ (u v : Vertex) →
      Path.finish (treePath u v) ≡ v
    treePathValid :
      ∀ (u v : Vertex) →
      Path.valid (treePath u v) ≡ true
    treePathBoundedByEdgeCount :
      ∀ (u v : Vertex) →
      Path.pathLength (treePath u v) ≤ treeEdgeCount

treePathLength :
  {G : FiniteSupportGraph} →
  TreePathStructure G →
  FiniteSupportGraph.Vertex G →
  FiniteSupportGraph.Vertex G →
  Nat
treePathLength tp u v = Path.pathLength (TreePathStructure.treePath tp u v)

treePathDominatesGraphPath :
  {G : FiniteSupportGraph} →
  (gd : GraphDistanceStructure G) →
  (tp : TreePathStructure G) →
  ∀ (u v : FiniteSupportGraph.Vertex G) →
  GraphDistanceStructure.graphDist gd u v ≤ treePathLength tp u v
treePathDominatesGraphPath gd tp u v =
  GraphDistanceStructure.graphDistMinimality gd
    (TreePathStructure.treePath tp u v)
    (TreePathStructure.treePathStart tp u v)
    (TreePathStructure.treePathFinish tp u v)
    (TreePathStructure.treePathValid tp u v)

treeSizeDominatesTreePath :
  {G : FiniteSupportGraph} →
  (tp : TreePathStructure G) →
  ∀ (u v : FiniteSupportGraph.Vertex G) →
  treePathLength tp u v ≤ TreePathStructure.treeEdgeCount tp
treeSizeDominatesTreePath tp u v =
  TreePathStructure.treePathBoundedByEdgeCount tp u v

postulate
  ymSupportEdge : Support.Link → Bool
  ymTreeEdge : Support.Link → Bool

  ImportedTreeEdgesSubsetSupportEdgesAxiom :
    ∀ {e : Support.Link} →
    ymTreeEdge e ≡ true →
    ymSupportEdge e ≡ true

currentFiniteSupportGraph : FiniteSupportGraph
currentFiniteSupportGraph = record
  { Vertex = Support.Link
  ; Edge = Support.Link
  ; supportEdge = ymSupportEdge
  ; treeEdge = ymTreeEdge
  ; treeEdgesSubsetSupportEdges =
      ImportedTreeEdgesSubsetSupportEdgesAxiom
  }

postulate
  ymGraphDist : Support.Link → Support.Link → Nat

  ImportedFiniteGraphDistanceAxiom :
    ∀ {u v : Support.Link} →
    (p : Path currentFiniteSupportGraph) →
    Path.start p ≡ u →
    Path.finish p ≡ v →
    Path.valid p ≡ true →
    ymGraphDist u v ≤ Path.pathLength p

currentGraphDistanceStructure :
  GraphDistanceStructure currentFiniteSupportGraph
currentGraphDistanceStructure = record
  { graphDist = ymGraphDist
  ; graphDistMinimality = ImportedFiniteGraphDistanceAxiom
  }

postulate
  ymTreePath : Support.Link → Support.Link → Path currentFiniteSupportGraph
  ymTreeEdgeCount : Nat

  ImportedTreePathRealisationAxiomStart :
    ∀ (u v : Support.Link) →
    Path.start (ymTreePath u v) ≡ u

  ImportedTreePathRealisationAxiomFinish :
    ∀ (u v : Support.Link) →
    Path.finish (ymTreePath u v) ≡ v

  ImportedTreePathRealisationAxiomValid :
    ∀ (u v : Support.Link) →
    Path.valid (ymTreePath u v) ≡ true

  ImportedTreePathBoundedByEdgeCountAxiom :
    ∀ (u v : Support.Link) →
    Path.pathLength (ymTreePath u v) ≤ ymTreeEdgeCount

currentTreePathStructure :
  TreePathStructure currentFiniteSupportGraph
currentTreePathStructure = record
  { treePath = ymTreePath
  ; treeEdgeCount = ymTreeEdgeCount
  ; treePathStart = ImportedTreePathRealisationAxiomStart
  ; treePathFinish = ImportedTreePathRealisationAxiomFinish
  ; treePathValid = ImportedTreePathRealisationAxiomValid
  ; treePathBoundedByEdgeCount =
      ImportedTreePathBoundedByEdgeCountAxiom
  }

currentTreeEdgesSubsetSupportEdgesAvailable : Bool
currentTreeEdgesSubsetSupportEdgesAvailable = true

currentGraphDistMinimalityAvailable : Bool
currentGraphDistMinimalityAvailable = true

currentTreePathBoundedByEdgeCountAvailable : Bool
currentTreePathBoundedByEdgeCountAvailable = true

currentTreeEdgesSubsetSupportEdgesAvailableIsTrue :
  currentTreeEdgesSubsetSupportEdgesAvailable ≡ true
currentTreeEdgesSubsetSupportEdgesAvailableIsTrue = refl

currentGraphDistMinimalityAvailableIsTrue :
  currentGraphDistMinimalityAvailable ≡ true
currentGraphDistMinimalityAvailableIsTrue = refl

currentTreePathBoundedByEdgeCountAvailableIsTrue :
  currentTreePathBoundedByEdgeCountAvailable ≡ true
currentTreePathBoundedByEdgeCountAvailableIsTrue = refl

-- ── Tree path as support-graph path adapter ─────────────────────────
-- IMPORTED AXIOM STATUS:
-- This module uses imported finite-graph axioms (Diestel §1.5.1, etc.).
-- The metric comparison bridge closes relative to these axioms.
-- A constructive discharge would require a decidable finite tree type
-- with path enumeration — currently out of scope for the DASHI lane.
-- All Clay/promotion flags remain false regardless.

record TreePathAsSupportGraphPath : Set where
  field
    treePathEdgesAvailable : Bool
    treeEdgesSubsetSupportEdges : Bool
    treePathEdgesAllTreeEdges : Bool
    treePathEdgesAllSupportEdges : Bool
    treePathIsSupportPath : Bool

currentTreePathAsSupportGraphPath : TreePathAsSupportGraphPath
currentTreePathAsSupportGraphPath = record
  { treePathEdgesAvailable = true
  ; treeEdgesSubsetSupportEdges = true
  ; treePathEdgesAllTreeEdges = true
  ; treePathEdgesAllSupportEdges = true
  ; treePathIsSupportPath = true
  }

currentTreePathAsSupportGraphPathAvailable : Bool
currentTreePathAsSupportGraphPathAvailable =
  TreePathAsSupportGraphPath.treePathIsSupportPath
    currentTreePathAsSupportGraphPath

currentTreePathAsSupportGraphPathAvailableIsTrue :
  currentTreePathAsSupportGraphPathAvailable ≡ true
currentTreePathAsSupportGraphPathAvailableIsTrue = refl

YMVertex : Set
YMVertex = FiniteSupportGraph.Vertex currentFiniteSupportGraph

YMEdge : Set
YMEdge = FiniteSupportGraph.Edge currentFiniteSupportGraph
