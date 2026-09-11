module DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- DASHI KNOWLEDGE TRAVERSAL FUNNEL
--
-- Cross-pollinated from Ibrahim, Danforth, Dodds (2017), Wikipedia First
-- Link Network, DOI 10.1016/j.jocs.2016.12.001.  External identity,
-- bibliography and classification remain coordinates; they do not become
-- proof, authority or formulation ownership.
------------------------------------------------------------------------

record DashiKnowledgeCoordinate : Set where
  constructor dashi-knowledge-coordinate
  field
    modulePath : String
    formulationOwner : String
    deweyParent : String
    primaryQid : String
    primarySourceId : String
open DashiKnowledgeCoordinate public

data DashiKnowledgeEdgeKind : Set where
  formulatedBy : DashiKnowledgeEdgeKind
  dependsOn : DashiKnowledgeEdgeKind
  generalisesTo : DashiKnowledgeEdgeKind
  supportedBy : DashiKnowledgeEdgeKind
  crossPollinatesWith : DashiKnowledgeEdgeKind
  externallyIdentifiedBy : DashiKnowledgeEdgeKind

record DashiFirstLinkPolicy : Set where
  constructor dashi-first-link-policy
  field
    preferExplicitFormulationOwner : Bool
    preferTypedDependency : Bool
    preferTypedGeneralisation : Bool
    sourceIdentityIsCoordinateOnly : Bool
    qidIsCoordinateOnly : Bool
    deweyIsCoordinateOnly : Bool
    lexicalFallbackAllowed : Bool
open DashiFirstLinkPolicy public

canonicalDashiFirstLinkPolicy : DashiFirstLinkPolicy
canonicalDashiFirstLinkPolicy =
  dashi-first-link-policy true true true true true true false

record DashiFirstLinkEdge : Set where
  constructor dashi-first-link-edge
  field
    from : DashiKnowledgeCoordinate
    to : DashiKnowledgeCoordinate
    kind : DashiKnowledgeEdgeKind
    selectionPolicy : DashiFirstLinkPolicy
    rationale : String
    sourceAttributed : Bool
open DashiFirstLinkEdge public

record DashiFormulationAnchor : Set where
  constructor dashi-formulation-anchor
  field
    coordinate : DashiKnowledgeCoordinate
    ownerMeaning : String
    sourceBoundaryRetained : Bool
open DashiFormulationAnchor public

record AnchoredKnowledgeNode : Set where
  constructor anchored-knowledge-node
  field
    coordinate : DashiKnowledgeCoordinate
    anchor : DashiFormulationAnchor
open AnchoredKnowledgeNode public

data DashiTraversalOutcome : Set where
  reachedFormulationAnchor : DashiTraversalOutcome
  enteredCycle : DashiTraversalOutcome
  deadEnd : DashiTraversalOutcome
  unresolved : DashiTraversalOutcome

record DashiTraversalReceipt : Set where
  constructor dashi-traversal-receipt
  field
    start : DashiKnowledgeCoordinate
    terminal : DashiKnowledgeCoordinate
    hops : Nat
    outcome : DashiTraversalOutcome
    policy : DashiFirstLinkPolicy
    graphRevision : String
    empiricallyComputed : Bool
open DashiTraversalReceipt public

record DashiTraversalFunnelReceipt : Set where
  constructor dashi-traversal-funnel-receipt
  field
    anchor : DashiFormulationAnchor
    graphRevision : String
    nodesObserved : Nat
    pathsDirectedThroughAnchor : Nat
    maximumObservedDepth : Nat
    funnelRank : Nat
    empiricalOnly : Bool
open DashiTraversalFunnelReceipt public

record DashiCoverageVector : Set where
  constructor dashi-coverage-vector
  field
    moduleDepth : Nat
    sourceBearingModules : Nat
    qidBearingModules : Nat
    provenanceBearingModules : Nat
    graphConnectedModules : Nat
open DashiCoverageVector public

data DeweyAdjacencyCreatesSemanticEdge : Set where
data QidIdentityCreatesProof : Set where
data FirstLinkCreatesTheoremImplication : Set where
data TraversalFunnelRankCreatesAuthority : Set where
data ExternalKnowledgeGraphReplacesDashiOwner : Set where

deweyAdjacencyIsNotSemanticEdge : DeweyAdjacencyCreatesSemanticEdge → ⊥
deweyAdjacencyIsNotSemanticEdge ()

qidIdentityIsNotProof : QidIdentityCreatesProof → ⊥
qidIdentityIsNotProof ()

firstLinkIsNotTheoremImplication : FirstLinkCreatesTheoremImplication → ⊥
firstLinkIsNotTheoremImplication ()

funnelRankIsNotAuthority : TraversalFunnelRankCreatesAuthority → ⊥
funnelRankIsNotAuthority ()

externalGraphDoesNotReplaceDashiOwner : ExternalKnowledgeGraphReplacesDashiOwner → ⊥
externalGraphDoesNotReplaceDashiOwner ()

record DashiKnowledgeTraversalBoundary : Set where
  constructor dashi-knowledge-traversal-boundary
  field
    deterministicPolicy : Bool
    formulationAnchored : Bool
    deweySeparated : Bool
    qidSeparated : Bool
    sourceSeparated : Bool
    funnelIsEmpirical : Bool
    centralityPromotesProofAuthority : Bool
open DashiKnowledgeTraversalBoundary public

canonicalDashiKnowledgeTraversalBoundary : DashiKnowledgeTraversalBoundary
canonicalDashiKnowledgeTraversalBoundary =
  dashi-knowledge-traversal-boundary true true true true true true false
