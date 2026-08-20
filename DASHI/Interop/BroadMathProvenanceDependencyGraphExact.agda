module DASHI.Interop.BroadMathProvenanceDependencyGraphExact where

------------------------------------------------------------------------
-- BROAD-MATH PROVENANCE / DEPENDENCY GRAPH
--
-- This is the theorem-facing source map for the current convergence tranche.
-- It deliberately separates:
--
--   source family        (DASHI / Wikidata / JMD Lean / BFO / literature...)
--   dependency role      (definition / evidence / projection / rechart...)
--   requiredness         (load-bearing vs contextual)
--
-- Counts are descriptive provenance load.  They are not percentages of truth,
-- ownership, authority or confidence.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TypedProvenanceDependencyGraphExact as Graph
import DASHI.Core.AttributedSourceCore as Attr

------------------------------------------------------------------------
-- Target / formal nodes.
------------------------------------------------------------------------

argumentTransportNode : Graph.DependencyNode
argumentTransportNode = Graph.dependencyNode
  "provenance-preserving argument level transport"
  Graph.dashiFormal
  "retains whole argument and provenance across admitted level/rechart motion"
  false

proofObligationHyperformalismNode : Graph.DependencyNode
proofObligationHyperformalismNode = Graph.dependencyNode
  "level-indexed proof-obligation hyperformalism"
  Graph.dashiFormal
  "separates support polarity from applicability and required-axis completion"
  false

pnf369Node : Graph.DependencyNode
pnf369Node = Graph.dependencyNode
  "PNF 369 hyperfabric carrier"
  Graph.dashiFormal
  "3*3=9, 9^2=81, 3*3*3=27 address/weave carrier with p-adic/Monster labels"
  false

jPlusOneNode : Graph.DependencyNode
jPlusOneNode = Graph.dependencyNode
  "J+1 successor / fresh-unit bridge"
  Graph.dashiFormal
  "typed successor/rechart plus exact fresh-unit extension shape"
  false

justiceRoutingNode : Graph.DependencyNode
justiceRoutingNode = Graph.dependencyNode
  "situated justice and authority routing"
  Graph.dashiFormal
  "required axes, projection safety, non-compensation and route admissibility"
  false

crossDomainRegressionNode : Graph.DependencyNode
crossDomainRegressionNode = Graph.dependencyNode
  "brain-memory-pedagogy-atomics transport regression"
  Graph.dashiFormal
  "tests preservation-with-open-residual on four independent carriers"
  false

wikidataNode : Graph.DependencyNode
wikidataNode = Graph.dependencyNode
  "Wikidata statement / identifier surfaces"
  Graph.wikidataData
  "external graph facts and identifiers used only where a concrete adapter pins them"
  false

jmdLeanNode : Graph.DependencyNode
jmdLeanNode = Graph.dependencyNode
  "JMD Lean Wikidata formal contracts"
  Graph.jmdLeanFormal
  "external formal checker/alignment/quotient theorem surface; conformance is explicit where pinned"
  false

bfoNode : Graph.DependencyNode
bfoNode = Graph.dependencyNode
  "Basic Formal Ontology source commitments"
  Graph.bfoOntology
  "source ontology axioms/mappings for the cross-ontology diagnosis lane"
  false

computedWitnessNode : Graph.DependencyNode
computedWitnessNode = Graph.dependencyNode
  "finite computed / runtime witness"
  Graph.computedWitness
  "finite diagnostic or arithmetic witness; scope remains bounded by its acquisition/model contract"
  false

runtimeAcquisitionNode : Graph.DependencyNode
runtimeAcquisitionNode = Graph.dependencyNode
  "SensibLaw / Zelph / WDQS acquisition"
  Graph.runtimeAcquisition
  "candidate discovery and graph traversal; acquisition is not semantic authority"
  false

sweetgrassNode : Graph.DependencyNode
sweetgrassNode = Graph.dependencyNode
  "Robin Wall Kimmerer / Braiding Sweetgrass attribution"
  Graph.communityCulturalSource
  "braid/fabric interpretive provenance only; not mathematical theorem authority"
  false

literatureNode : Graph.DependencyNode
literatureNode = Graph.dependencyNode
  "scholarly source atlas"
  Graph.scholarlyLiterature
  "bounded conceptual/mathematical calibration with explicit promotion boundaries"
  false

canonicalBroadNodes : List Graph.DependencyNode
canonicalBroadNodes =
  argumentTransportNode
  ∷ proofObligationHyperformalismNode
  ∷ pnf369Node
  ∷ jPlusOneNode
  ∷ justiceRoutingNode
  ∷ crossDomainRegressionNode
  ∷ wikidataNode
  ∷ jmdLeanNode
  ∷ bfoNode
  ∷ computedWitnessNode
  ∷ runtimeAcquisitionNode
  ∷ sweetgrassNode
  ∷ literatureNode
  ∷ []

------------------------------------------------------------------------
-- Typed edges.  Contextual edges are deliberately marked required=false.
------------------------------------------------------------------------

canonicalBroadEdges : List Graph.DependencyEdge
canonicalBroadEdges =
  Graph.dependencyEdge
    pnf369Node argumentTransportNode Graph.residualRole true
    "369/hyperfabric supplies address/weave geometry; argument identity is retained separately"
  ∷ Graph.dependencyEdge
    jPlusOneNode argumentTransportNode Graph.rechartRole true
    "J+1 supplies typed successor/rechart shape without identifying modular-j or representation-j"
  ∷ Graph.dependencyEdge
    argumentTransportNode proofObligationHyperformalismNode Graph.reconstructionRole true
    "proof-obligation stalks retain claim/provenance across level transport"
  ∷ Graph.dependencyEdge
    proofObligationHyperformalismNode justiceRoutingNode Graph.theoremRole true
    "support/applicability/required-axis separation constrains authority routing"
  ∷ Graph.dependencyEdge
    argumentTransportNode crossDomainRegressionNode Graph.theoremRole true
    "common transport law is adversarially tested on brain, memory, pedagogy and atomics"
  ∷ Graph.dependencyEdge
    literatureNode proofObligationHyperformalismNode Graph.vocabularyRole false
    "Belnap/Dunn/Crenshaw and domain literature calibrate vocabulary/boundaries; DASHI owns the new theorem"
  ∷ Graph.dependencyEdge
    sweetgrassNode pnf369Node Graph.vocabularyRole false
    "braid/fabric motif attribution; no mathematical proof imported"
  ∷ Graph.dependencyEdge
    wikidataNode jmdLeanNode Graph.evidenceRole true
    "JMD's Wikidata checker consumes a declared Wikidata knowledge model/input"
  ∷ Graph.dependencyEdge
    bfoNode jmdLeanNode Graph.alignmentRole false
    "BFO becomes load-bearing only for a pinned BFO↔Wikidata alignment/case"
  ∷ Graph.dependencyEdge
    runtimeAcquisitionNode computedWitnessNode Graph.acquisitionRole true
    "runtime traversal supplies bounded candidate/witness material"
  ∷ Graph.dependencyEdge
    computedWitnessNode justiceRoutingNode Graph.validationRole false
    "computed witnesses can test formal carriers but do not create normative authority"
  ∷ []

canonicalBroadDependencyGraph : Graph.TypedDependencyGraph
canonicalBroadDependencyGraph =
  Graph.typedDependencyGraph
    "DASHI broad-math / ontology / governance dependency map"
    canonicalBroadNodes
    canonicalBroadEdges

canonicalBroadLoad : Graph.ProvenanceLoadSummary
canonicalBroadLoad = Graph.summarizeProvenanceLoad canonicalBroadDependencyGraph

canonicalBroadTotalNodesIsThirteen :
  Graph.totalNodes canonicalBroadLoad ≡ 13
canonicalBroadTotalNodesIsThirteen = refl

canonicalBroadTotalEdgesIsEleven :
  Graph.totalEdges canonicalBroadLoad ≡ 11
canonicalBroadTotalEdgesIsEleven = refl

canonicalBroadDashiNodesIsSix :
  Graph.dashiNodes canonicalBroadLoad ≡ 6
canonicalBroadDashiNodesIsSix = refl

canonicalBroadWikidataNodesIsOne :
  Graph.wikidataNodes canonicalBroadLoad ≡ 1
canonicalBroadWikidataNodesIsOne = refl

canonicalBroadJMDLeanNodesIsOne :
  Graph.jmdLeanNodes canonicalBroadLoad ≡ 1
canonicalBroadJMDLeanNodesIsOne = refl

canonicalBroadBFONodesIsOne :
  Graph.bfoNodes canonicalBroadLoad ≡ 1
canonicalBroadBFONodesIsOne = refl

canonicalBroadLiteratureNodesIsOne :
  Graph.literatureNodes canonicalBroadLoad ≡ 1
canonicalBroadLiteratureNodesIsOne = refl

canonicalBroadComputedNodesIsOne :
  Graph.computedNodes canonicalBroadLoad ≡ 1
canonicalBroadComputedNodesIsOne = refl

canonicalBroadCulturalNodesIsOne :
  Graph.culturalNodes canonicalBroadLoad ≡ 1
canonicalBroadCulturalNodesIsOne = refl

canonicalBroadRuntimeNodesIsOne :
  Graph.runtimeNodes canonicalBroadLoad ≡ 1
canonicalBroadRuntimeNodesIsOne = refl

------------------------------------------------------------------------
-- Concrete scholarly attribution rows used by this convergence surface.
------------------------------------------------------------------------

conwayNortonSource : Attr.AttributedSource
conwayNortonSource = Attr.mkDOISource
  "John H. Conway; Simon P. Norton"
  "Monstrous Moonshine"
  "Bulletin of the London Mathematical Society 11"
  "1979"
  "10.1112/blms/11.3.308"
  "https://doi.org/10.1112/blms/11.3.308"
  Attr.academicArticleSource
  "Source calibration for the exact Monster/McKay arithmetic already imported by the repository; does not identify the local J+1 chart carrier with the modular j-function."
  Attr.publicAttribution

borcherdsSource : Attr.AttributedSource
borcherdsSource = Attr.mkDOISource
  "Richard E. Borcherds"
  "Monstrous Moonshine and Monstrous Lie Superalgebras"
  "Inventiones Mathematicae 109"
  "1992"
  "10.1007/BF01232032"
  "https://doi.org/10.1007/BF01232032"
  Attr.academicArticleSource
  "Moonshine theorem provenance; no semantic identification with DASHI chart, cognition, governance or 369 carriers follows."
  Attr.publicAttribution

belnapSource : Attr.AttributedSource
belnapSource = Attr.mkDOISource
  "Nuel D. Belnap"
  "A Useful Four-Valued Logic"
  "Modern Uses of Multiple-Valued Logic"
  "1977"
  "10.1007/978-94-010-1161-7_2"
  "https://doi.org/10.1007/978-94-010-1161-7_2"
  Attr.academicChapterSource
  "Motivates independent positive/negative information coordinates only; level applicability and required-axis routing are DASHI constructions."
  Attr.publicAttribution

crenshawSource : Attr.AttributedSource
crenshawSource = Attr.mkDOISource
  "Kimberle Williams Crenshaw"
  "Mapping the Margins: Intersectionality, Identity Politics, and Violence against Women of Color"
  "Stanford Law Review 43(6)"
  "1991"
  "10.2307/1229039"
  "https://doi.org/10.2307/1229039"
  Attr.academicArticleSource
  "Motivates situated/non-factorability discipline; the generic factorisation theorem is DASHI mathematics rather than a theorem attributed to Crenshaw."
  Attr.publicAttribution

kimmererSource : Attr.AttributedSource
kimmererSource = Attr.mkNoDOISource
  "Robin Wall Kimmerer"
  "Braiding Sweetgrass: Indigenous Wisdom, Scientific Knowledge, and the Teachings of Plants"
  "Milkweed Editions"
  "2013"
  "https://www.wikidata.org/entity/Q85748689"
  Attr.academicBookSource
  "Explicit interpretive provenance for braid/fabric vocabulary; no fibre-product, sheaf, ontology or mathematical theorem is attributed to the book."
  Attr.publicAttribution

canonicalBroadAttributedSources : List Attr.AttributedSource
canonicalBroadAttributedSources =
  conwayNortonSource
  ∷ borcherdsSource
  ∷ belnapSource
  ∷ crenshawSource
  ∷ kimmererSource
  ∷ []

canonicalBroadSourceAtlas : Attr.AttributedSourceAtlas
canonicalBroadSourceAtlas = Attr.mkSourceAtlas
  "broad 369/J+1/fibre/argument-transport cross-pollination sources"
  "DASHI.Interop.BroadMathProvenanceDependencyGraphExact"
  canonicalBroadAttributedSources
  "Source calibration and cultural attribution for the broad-math convergence; citations do not import proof or authority."

canonicalBroadSourceAtlasDoesNotCreateAuthority :
  Attr.atlasCreatesAuthority canonicalBroadSourceAtlas ≡ false
canonicalBroadSourceAtlasDoesNotCreateAuthority =
  Attr.atlasCreatesAuthorityIsFalse canonicalBroadSourceAtlas

record BroadMathProvenanceBoundary : Set where
  constructor broadMathProvenanceBoundary
  field
    sourceCountsAreTruthPercentages : Bool
    culturalAttributionIsMathAuthority : Bool
    JMDNodeMeansLeanAndAgdaAreDefinitionallyEqual : Bool
    BFOContextMeansAllWikidataClaimsUseBFO : Bool
    typedEdgesExposeDependencyRole : Bool

canonicalBroadMathProvenanceBoundary : BroadMathProvenanceBoundary
canonicalBroadMathProvenanceBoundary =
  broadMathProvenanceBoundary false false false false true
