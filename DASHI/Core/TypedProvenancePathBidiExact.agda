module DASHI.Core.TypedProvenancePathBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AmplificationLineageBidiCrossPollination2026Exact as Lineage
import DASHI.Biology.DrosophilaSameTrialProvenanceDependenceExact as Fly

------------------------------------------------------------------------
-- TYPED PROVENANCE PATH
--
-- Cross-weld of root dependence and lineage-edge semantics.  Root overlap
-- answers whether two evidence units share provenance support; edge kinds
-- answer how one artifact was generated/transformed/reported/amplified.  The
-- two coordinates are intentionally not collapsed.
------------------------------------------------------------------------

record TypedProvenancePath : Set where
  constructor typed-provenance-path
  field
    left : Lineage.LineageNode
    right : Lineage.LineageNode
    sharedRoot : Lineage.SharedRootWitness left right
    edgeKinds : List Lineage.LineageEdgeKind
    dependenceRelation : Fly.EvidenceRelation
    pathReference : String

open TypedProvenancePath public

record RootDependenceReading (path : TypedProvenancePath) : Set where
  constructor root-dependence-reading
  field
    relation : Fly.EvidenceRelation
    relationMatchesPath : relation ≡ dependenceRelation path
    edgeSemanticsReference : String
    rootSupportReference : String

open RootDependenceReading public

canonicalRootDependenceReading :
  (path : TypedProvenancePath) → RootDependenceReading path
canonicalRootDependenceReading path =
  root-dependence-reading
    (dependenceRelation path)
    refl
    "lineage edge semantics are retained separately from dependence class"
    (Lineage.leftPathReference (sharedRoot path))

------------------------------------------------------------------------
-- Exact finite witness: identical root dependence can coexist with distinct
-- lineage semantics.  Therefore dependence class does not recover edge kind.
------------------------------------------------------------------------

sourceNode : Lineage.LineageNode
sourceNode = Lineage.lineage-node "source" "synthetic root source"

reportNode : Lineage.LineageNode
reportNode = Lineage.lineage-node "report" "synthetic report descendant"

amplifiedNode : Lineage.LineageNode
amplifiedNode = Lineage.lineage-node "amplified" "synthetic amplified descendant"

sharedSourceReport : Lineage.SharedRootWitness sourceNode reportNode
sharedSourceReport = Lineage.shared-root-witness sourceNode "root->source" "root->report"

sharedSourceAmplified : Lineage.SharedRootWitness sourceNode amplifiedNode
sharedSourceAmplified = Lineage.shared-root-witness sourceNode "root->source" "root->amplified"

reportedPath : TypedProvenancePath
reportedPath = typed-provenance-path
  sourceNode reportNode sharedSourceReport
  (Lineage.reportedBy ∷ [])
  Fly.sharedPipelineCorroboration
  "synthetic shared-root report path"

amplifiedPath : TypedProvenancePath
amplifiedPath = typed-provenance-path
  sourceNode amplifiedNode sharedSourceAmplified
  (Lineage.amplifiedBy ∷ [])
  Fly.sharedPipelineCorroboration
  "synthetic shared-root amplification path"

sameDependenceDifferentSemantics :
  dependenceRelation reportedPath ≡ dependenceRelation amplifiedPath
sameDependenceDifferentSemantics = refl

reportedNotAmplified : Lineage.reportedBy ≡ Lineage.amplifiedBy → ⊥
reportedNotAmplified ()

data DependenceClassDeterminesLineageSemantics : Set where
data LineageSemanticsAloneProvesIndependence : Set where

dependenceClassDoesNotDetermineLineageSemantics :
  DependenceClassDeterminesLineageSemantics → ⊥
dependenceClassDoesNotDetermineLineageSemantics ()

lineageSemanticsAloneDoesNotProveIndependence :
  LineageSemanticsAloneProvesIndependence → ⊥
lineageSemanticsAloneDoesNotProveIndependence ()

record TypedProvenancePathBoundary : Set where
  constructor typed-provenance-path-boundary
  field
    rootSupportAndEdgeSemanticsSeparated : Bool
    sameDependenceMayHaveDifferentEdgeSemantics : Bool
    edgeKindAloneProvesIndependentRoots : Bool

canonicalTypedProvenancePathBoundary : TypedProvenancePathBoundary
canonicalTypedProvenancePathBoundary =
  typed-provenance-path-boundary true true false
