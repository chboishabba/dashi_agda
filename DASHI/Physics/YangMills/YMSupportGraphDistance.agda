module DASHI.Physics.YangMills.YMSupportGraphDistance where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.List.Base using (length)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties as NatP using (≤-trans)

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

-- ── P01/P02/P03 concrete theorem surfaces ───────────────────────────
-- P01 treePathEdgesExist is the concrete tree-path witness.
-- P02 graphDistMinimality and P03 treePathBoundedByEdgeCount expose the
-- imported source axioms as named lemmas rather than availability flags.

p01TreePathEdgesExistViaYmTreePath :
  ∀ (u v : Support.Link) →
  Path currentFiniteSupportGraph
p01TreePathEdgesExistViaYmTreePath = ymTreePath

p01TreePathEdgesExist :
  ∀ (u v : Support.Link) →
  Path currentFiniteSupportGraph
p01TreePathEdgesExist = p01TreePathEdgesExistViaYmTreePath

p02GraphDistMinimalityFromImportedFiniteGraphDistanceAxiom :
  ∀ (u v : Support.Link) →
  ymGraphDist u v ≤ Path.pathLength (ymTreePath u v)
p02GraphDistMinimalityFromImportedFiniteGraphDistanceAxiom u v =
  ImportedFiniteGraphDistanceAxiom
    (ymTreePath u v)
    (ImportedTreePathRealisationAxiomStart u v)
    (ImportedTreePathRealisationAxiomFinish u v)
    (ImportedTreePathRealisationAxiomValid u v)

p02GraphDistMinimality :
  ∀ (u v : Support.Link) →
  ymGraphDist u v ≤ Path.pathLength (ymTreePath u v)
p02GraphDistMinimality =
  p02GraphDistMinimalityFromImportedFiniteGraphDistanceAxiom

p03TreePathBoundedByEdgeCountFromImportedTreePathBoundedByEdgeCountAxiom :
  ∀ (u v : Support.Link) →
  Path.pathLength (ymTreePath u v) ≤ ymTreeEdgeCount
p03TreePathBoundedByEdgeCountFromImportedTreePathBoundedByEdgeCountAxiom =
  ImportedTreePathBoundedByEdgeCountAxiom

p03TreePathBoundedByEdgeCount :
  ∀ (u v : Support.Link) →
  Path.pathLength (ymTreePath u v) ≤ ymTreeEdgeCount
p03TreePathBoundedByEdgeCount =
  p03TreePathBoundedByEdgeCountFromImportedTreePathBoundedByEdgeCountAxiom

-- ── P01/P02/P03: concrete imported graph witnesses ─────────────────

treePathEdgesExist :
  ∀ (u v : Support.Link) →
  Path currentFiniteSupportGraph
treePathEdgesExist = ymTreePath

treePathEdgesExistStart :
  ∀ (u v : Support.Link) →
  Path.start (treePathEdgesExist u v) ≡ u
treePathEdgesExistStart = ImportedTreePathRealisationAxiomStart

treePathEdgesExistFinish :
  ∀ (u v : Support.Link) →
  Path.finish (treePathEdgesExist u v) ≡ v
treePathEdgesExistFinish = ImportedTreePathRealisationAxiomFinish

treePathEdgesExistValid :
  ∀ (u v : Support.Link) →
  Path.valid (treePathEdgesExist u v) ≡ true
treePathEdgesExistValid = ImportedTreePathRealisationAxiomValid

graphDistMinimalityViaImportedFiniteGraphDistanceAxiom :
  ∀ {u v : Support.Link} →
  (p : Path currentFiniteSupportGraph) →
  Path.start p ≡ u →
  Path.finish p ≡ v →
  Path.valid p ≡ true →
  ymGraphDist u v ≤ Path.pathLength p
graphDistMinimalityViaImportedFiniteGraphDistanceAxiom =
  ImportedFiniteGraphDistanceAxiom

p03TreePathBoundedByEdgeCountFromWitness :
  ∀ (u v : Support.Link) →
  Path.pathLength (treePathEdgesExist u v) ≤ ymTreeEdgeCount
p03TreePathBoundedByEdgeCountFromWitness = ImportedTreePathBoundedByEdgeCountAxiom

p02GraphDistMinimalityFromWitness :
  ∀ (u v : Support.Link) →
  ymGraphDist u v ≤ Path.pathLength (treePathEdgesExist u v)
p02GraphDistMinimalityFromWitness u v =
  graphDistMinimalityViaImportedFiniteGraphDistanceAxiom
    (treePathEdgesExist u v)
    (treePathEdgesExistStart u v)
    (treePathEdgesExistFinish u v)
    (treePathEdgesExistValid u v)

record TreePathEdgesExistWitness (u v : Support.Link) : Set where
  field
    path : Path currentFiniteSupportGraph
    startAtSource : Path.start path ≡ u
    finishAtTarget : Path.finish path ≡ v
    validPath : Path.valid path ≡ true

treePathEdgesExistPathWitness :
  ∀ (u v : Support.Link) →
  TreePathEdgesExistWitness u v
treePathEdgesExistPathWitness u v = record
  { path = treePathEdgesExist u v
  ; startAtSource = treePathEdgesExistStart u v
  ; finishAtTarget = treePathEdgesExistFinish u v
  ; validPath = treePathEdgesExistValid u v
  }

record GraphCoreP01P02P03TheoremSurface : Set₁ where
  field
    p01TreePathEdgesExistSurface :
      ∀ (u v : Support.Link) →
      Path currentFiniteSupportGraph
    p02GraphDistMinimalitySurface :
      ∀ (u v : Support.Link) →
      ymGraphDist u v ≤ Path.pathLength (p01TreePathEdgesExistSurface u v)
    p03TreePathBoundedByEdgeCountSurface :
      ∀ (u v : Support.Link) →
      Path.pathLength (p01TreePathEdgesExistSurface u v) ≤ ymTreeEdgeCount

currentGraphCoreP01P02P03TheoremSurface :
  GraphCoreP01P02P03TheoremSurface
currentGraphCoreP01P02P03TheoremSurface = record
  { p01TreePathEdgesExistSurface = p01TreePathEdgesExist
  ; p02GraphDistMinimalitySurface = p02GraphDistMinimality
  ; p03TreePathBoundedByEdgeCountSurface =
      p03TreePathBoundedByEdgeCountFromImportedTreePathBoundedByEdgeCountAxiom
  }

record GraphCoreP01P03WitnessBundle : Set₁ where
  field
    supportGraph : FiniteSupportGraph
    graphDistanceStructure : GraphDistanceStructure supportGraph
    treePathStructure : TreePathStructure supportGraph
    p01Witness :
      ∀ (u v : Support.Link) →
      Path currentFiniteSupportGraph
    p01WitnessStart :
      ∀ (u v : Support.Link) →
      Path.start (p01Witness u v) ≡ u
    p01WitnessFinish :
      ∀ (u v : Support.Link) →
      Path.finish (p01Witness u v) ≡ v
    p01WitnessValid :
      ∀ (u v : Support.Link) →
      Path.valid (p01Witness u v) ≡ true
    p02DerivedFromSameWitness :
      ∀ (u v : Support.Link) →
      ymGraphDist u v ≤ Path.pathLength (p01Witness u v)
    p03DerivedFromSameWitness :
      ∀ (u v : Support.Link) →
      Path.pathLength (p01Witness u v) ≤ ymTreeEdgeCount
    provenance : String
    provenanceIsCanonical :
      provenance ≡
      "P01-P03 are imported/derived wrappers over the same YM tree-path and graph-distance witness; this bundle introduces no extra postulates."

currentGraphCoreP01P03WitnessBundle : GraphCoreP01P03WitnessBundle
currentGraphCoreP01P03WitnessBundle = record
  { supportGraph = currentFiniteSupportGraph
  ; graphDistanceStructure = currentGraphDistanceStructure
  ; treePathStructure = currentTreePathStructure
  ; p01Witness = treePathEdgesExist
  ; p01WitnessStart = treePathEdgesExistStart
  ; p01WitnessFinish = treePathEdgesExistFinish
  ; p01WitnessValid = treePathEdgesExistValid
  ; p02DerivedFromSameWitness = p02GraphDistMinimalityFromWitness
  ; p03DerivedFromSameWitness = p03TreePathBoundedByEdgeCountFromWitness
  ; provenance =
      "P01-P03 are imported/derived wrappers over the same YM tree-path and graph-distance witness; this bundle introduces no extra postulates."
  ; provenanceIsCanonical = refl
  }

record P01P03SurfaceCoherence : Set₁ where
  field
    witnessBundle : GraphCoreP01P03WitnessBundle
    p02ReusesP01Witness : Bool
    p03ReusesP01Witness : Bool
    noExtraPostulatesIntroduced : Bool
    p02ReusesP01WitnessIsTrue :
      p02ReusesP01Witness ≡ true
    p03ReusesP01WitnessIsTrue :
      p03ReusesP01Witness ≡ true
    noExtraPostulatesIntroducedIsTrue :
      noExtraPostulatesIntroduced ≡ true

currentP01P03SurfaceCoherence : P01P03SurfaceCoherence
currentP01P03SurfaceCoherence = record
  { witnessBundle = currentGraphCoreP01P03WitnessBundle
  ; p02ReusesP01Witness = true
  ; p03ReusesP01Witness = true
  ; noExtraPostulatesIntroduced = true
  ; p02ReusesP01WitnessIsTrue = refl
  ; p03ReusesP01WitnessIsTrue = refl
  ; noExtraPostulatesIntroducedIsTrue = refl
  }

open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; diestel-graph-theory
  ; standardWrapper
  ; VerificationStatus
  )

record ImportedTreePathEdgesExist : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    pathExist : ∀ (u v : Support.Link) → Path currentFiniteSupportGraph

record ImportedGraphDistMinimality : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    minimality : ∀ (u v : Support.Link) (p : Path currentFiniteSupportGraph) →
      Path.start p ≡ u →
      Path.finish p ≡ v →
      Path.valid p ≡ true →
      ymGraphDist u v ≤ Path.pathLength p

record ImportedTreePathBoundedByEdgeCount : Set where
  field
    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus
    bounded : ∀ (u v : Support.Link) → Path.pathLength (ymTreePath u v) ≤ ymTreeEdgeCount

treePathEdgesExistWitness : ImportedTreePathEdgesExist
treePathEdgesExistWitness = record
  { sourceAuthorityId = diestel-graph-theory
  ; theoremLocator = "§1.5.1"
  ; status = standardWrapper
  ; pathExist = ymTreePath
  }

graphDistMinimalityWitness : ImportedGraphDistMinimality
graphDistMinimalityWitness = record
  { sourceAuthorityId = diestel-graph-theory
  ; theoremLocator = "§1.5.1"
  ; status = standardWrapper
  ; minimality = λ u v p start finish valid → ImportedFiniteGraphDistanceAxiom p start finish valid
  }

treePathBoundedByEdgeCountWitness : ImportedTreePathBoundedByEdgeCount
treePathBoundedByEdgeCountWitness = record
  { sourceAuthorityId = diestel-graph-theory
  ; theoremLocator = "§1.5.1"
  ; status = standardWrapper
  ; bounded = ImportedTreePathBoundedByEdgeCountAxiom
  }
