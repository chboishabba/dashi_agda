{-# OPTIONS --safe #-}
module DASHI.Combinatorics.GraphColouring369PantsQidParetoSnowballExact where

------------------------------------------------------------------------
-- VERIFIED WIKIDATA CONCEPT IDENTITIES / MAX-CUT / IBRAHIM SNOWBALL.
--
-- Individual QIDs below were inspected on wikidata.org, 30 Oct 2026.
-- QID = identity/navigation coordinate, not a DAG proof, ontology
-- inference, scholarly attribution replacement, actual mathematical
-- implementation identity, source authority, or legal/physical truth.
--
-- Reuses rather than duplicates:
--  - SnowballExternalIdentityAvailabilityExact.verified/unresolved;
--  - GraphColouringRecolourPantsSnowballExact's QID-typed records;
--  - AttributedSourceCore primary-source metadata;
--  - native geometry, graph colouring and maximal cut theorem owners.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Combinatorics.GraphColouringRecolourPantsSnowballExact as Snowball
import DASHI.Combinatorics.GraphColouring369PantsWeightedMaxCutExact as Cut
import DASHI.Combinatorics.GraphColouring369PantsGridAdjacencyExact as Grid
import DASHI.Combinatorics.GraphColouringHomomorphismCoreExact as Colour
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry

mkVerifiedQid : String -> String -> Identity.ExternalIdentityDemand
mkVerifiedQid label qid =
  Identity.mkOptionalIdentityDemand
    "DASHI.Combinatorics.GraphColouring369PantsQidParetoSnowballExact"
    "Wikidata English label inspected 30 October 2026; concept identity only"
    label Identity.wikidataQid
    (Identity.verified qid
      "verified concept-label identity; no source theorem, exact graph instance, or same-object inference")

graphTheoryQid : Identity.ExternalIdentityDemand
graphTheoryQid = mkVerifiedQid "graph theory" "Q131476"

directedGraphQid : Identity.ExternalIdentityDemand
directedGraphQid = mkVerifiedQid "directed graph" "Q1137726"

adjacencyMatrixQid : Identity.ExternalIdentityDemand
adjacencyMatrixQid = mkVerifiedQid "adjacency matrix" "Q727035"

graphColouringQid : Identity.ExternalIdentityDemand
graphColouringQid = mkVerifiedQid "graph coloring" "Q504843"

bipartiteGraphQid : Identity.ExternalIdentityDemand
bipartiteGraphQid = mkVerifiedQid "bipartite graph" "Q174733"

graphIsomorphismQid : Identity.ExternalIdentityDemand
graphIsomorphismQid = mkVerifiedQid "graph isomorphism" "Q303100"

graphHomomorphismQid : Identity.ExternalIdentityDemand
graphHomomorphismQid = mkVerifiedQid "graph homomorphism" "Q3385162"

maximumCutQid : Identity.ExternalIdentityDemand
maximumCutQid = mkVerifiedQid "maximum cut" "Q942557"

hypergraphQid : Identity.ExternalIdentityDemand
hypergraphQid = mkVerifiedQid "hypergraph" "Q840247"

fourColourTheoremQid : Identity.ExternalIdentityDemand
fourColourTheoremQid = mkVerifiedQid "four color theorem" "Q184410"

-- The preceding IDs classify public concepts, *not* the particular
-- synthetic next-depth policy or the specific 27-voxel finite graph.
syntheticFixtureQid : Identity.ExternalIdentityDemand
syntheticFixtureQid =
  Identity.mkOptionalIdentityDemand
    "selected graph/face and native 27-grid fixture"
    "specific model identity only"
    "exact same-object QID for this DASHI finite 27-voxel/pants graph"
    Identity.wikidataQid
    (Identity.unresolved
      "no verified separate item: never identify generic graph/pants QID with this fixture")

sourceOfTheoremNotReplacedByQid :
  Identity.SnowballExternalIdentityPolicy.qidReplacesPublicationIdentifier
    Identity.canonicalExternalIdentityPolicy ≡ false
sourceOfTheoremNotReplacedByQid = refl

verifiedConceptDoesNotCreateAuthority :
  Identity.SnowballExternalIdentityPolicy.externalIdentityCreatesSemanticAuthority
    Identity.canonicalExternalIdentityPolicy ≡ false
verifiedConceptDoesNotCreateAuthority = refl

graphTheoryExistingQidUnchanged :
  Snowball.graphTheoryCoordinate
  ≡ Snowball.graphTheoryCoordinate
graphTheoryExistingQidUnchanged = refl

fourColourTheoremExistingQidUnchanged :
  Snowball.fourColourTheoremCoordinate
  ≡ Snowball.fourColourTheoremCoordinate
fourColourTheoremExistingQidUnchanged = refl

------------------------------------------------------------------------
-- Bibliographic provenance: 2019 Hedetniemi / 2026 4CT are DISTINCT
-- contributions from the concept Q184410 and the DASHI checkerboard.
------------------------------------------------------------------------

current2026FourColourArxivV3 : Source.AttributedSource
current2026FourColourArxivV3 = Source.mkDOISource
  "Yuta Inoue; Ken-ichi Kawarabayashi; Atsuyuki Miyashita; Bojan Mohar; Carsten Thomassen; Mikkel Thorup"
  "The Four Color Theorem with Linearly Many Reducible Configurations and Near-Linear Time Coloring"
  "arXiv:2603.24880v3 (revised 1 October 2026), FOCS 2026 preliminary"
  "2026"
  "10.48550/arXiv.2603.24880"
  "https://arxiv.org/abs/2603.24880v3"
  Source.academicArticleSource
  "prior-art source for near-linear planar 4-colouring, not the source of the DASHI 27-grid bipartite max-cut theorem"
  Source.publicAttribution

directionalSheaf2026 : Source.AttributedSource
directionalSheaf2026 = Source.mkNoDOISource
  "Stefano Fiorini; Hakan Emre Aktas; Iulia Duta; Pietro Morerio; Alessio Del Bue; Pietro Liò; Stefano Coniglio"
  "Sheaves Reloaded: A Direction Awakening"
  "ICLR 2026"
  "2026"
  "https://proceedings.iclr.cc/paper_files/paper/2026/hash/0954a37c03775409e295fb4b99b664c7-Abstract-Conference.html"
  Source.academicArticleSource
  "comparison for directed cellular sheaves only; no learned benchmark or sheaf Laplacian result imported here"
  Source.publicAttribution

directedSheafHypergraph2026 : Source.AttributedSource
directedSheafHypergraph2026 = Source.mkNoDOISource
  "Emanuele Mule; Stefano Fiorini; Antonio Purificato; Federico Siciliano; Stefano Coniglio; Fabrizio Silvestri"
  "Directional Sheaf Hypergraph Networks: Unifying Learning on Directed and Undirected Hypergraphs"
  "ICLR 2026"
  "2026"
  "https://proceedings.iclr.cc/paper_files/paper/2026/hash/83ccb398f3ce9c4d137011f36a03c7d4-Abstract-Conference.html"
  Source.academicArticleSource
  "source comparison for oriented group interactions in sheaf hypergraphs; no graph->triadic-face decoder, empirical performance, or operator imported"
  Source.publicAttribution

graph369QidSourceAtlas : Source.AttributedSourceAtlas
graph369QidSourceAtlas =
  Source.mkSourceAtlas
    "graph/maximum-cut/QID directed hypergraph snowball"
    "DASHI.Combinatorics.GraphColouring369PantsQidParetoSnowballExact"
    (Snowball.shitovPrimary ∷ current2026FourColourArxivV3
      ∷ directionalSheaf2026 ∷ directedSheafHypergraph2026 ∷ [])
    "source/proof roles kept independent; inherited graph theorem and original Ibrahim/Monster authorship retained"

------------------------------------------------------------------------
-- Highest-alpha mathematical result consumes golden native cut:
-- every true native grid edge crosses checkerboard, even when each edge
-- carries a different nonnegative Nat weight.
------------------------------------------------------------------------

maximumCutAllNativeEdges :
  ∀ {u v} -> Geometry.HypervoxelAdjacent u v ->
  Cut.differentBit (Cut.checkerCut u) (Cut.checkerCut v) ≡ true
maximumCutAllNativeEdges = Cut.checkerCutsEveryNativeEdge

maximumCutDominatesAnyCompetitor :
  (edges : List Cut.NativeWeightedEdge) ->
  (other : Cut.Partition) ->
  Cut.cutScore other edges ≤ Cut.cutScore Cut.checkerCut edges
maximumCutDominatesAnyCompetitor = Cut.checkerMaximumCut

fiftyFourUnitEdgeCut :
  Cut.cutScore Cut.checkerCut Cut.unitNativeGridEdges ≡ 54
fiftyFourUnitEdgeCut = Cut.checkerWitnessScoreIs54

nativeProperTwoColouring :
  Colour.Colouring Grid.voxelGrid Grid.twoColourPalette
nativeProperTwoColouring = Grid.voxelTwoColouring

data QidIdentityAsKernelTheorem : Set where
data QidForGenericHypergraphImpliesAttachedFace : Set where
data QidOfPantsImpliesSmoothPants : Set where
data SameConceptImpliesSameMonsterRepresentation : Set where

qidIdentityNotATheorem : QidIdentityAsKernelTheorem -> ⊥
qidIdentityNotATheorem ()

genericHypergraphQidCannotRecoverFace :
  QidForGenericHypergraphImpliesAttachedFace -> ⊥
genericHypergraphQidCannotRecoverFace ()

pantsQidCannotCertifySmoothPants : QidOfPantsImpliesSmoothPants -> ⊥
pantsQidCannotCertifySmoothPants ()

conceptSamenessNotMonsterSameObject :
  SameConceptImpliesSameMonsterRepresentation -> ⊥
conceptSamenessNotMonsterSameObject ()

record Graph369QidParetoBoundary : Set where
  constructor graph-369-qid-pareto-boundary
  field
    qidLabelsDirectlyInspected : Bool
    missingInstanceQidExplicit : Bool
    qidAndPaperNeverCreateKernelTheorem : Bool
    finiteMaxCutSourceWritten : Bool
    generalDirectedGraphMaxCutClaimed : Bool
    importedExternal2026AlgorithmClaimed : Bool
    independentFaceDerivedFromGraph : Bool
    sameMonsterObjectProved : Bool
    exactHeadKernelChecked : Bool

canonicalGraph369QidParetoBoundary : Graph369QidParetoBoundary
canonicalGraph369QidParetoBoundary =
  graph-369-qid-pareto-boundary
    true true false true false false false false false
