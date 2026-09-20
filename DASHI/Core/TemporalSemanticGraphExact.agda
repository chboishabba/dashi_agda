module DASHI.Core.TemporalSemanticGraphExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- RENDERER-NEUTRAL TEMPORAL SYMBOL GRAPH
--
-- This module fixes the semantic objects that a source-history visualizer
-- may observe.  It deliberately says nothing about Manim, pixels, layout,
-- Tree-sitter, Git, or any concrete frontend.
------------------------------------------------------------------------

data SymbolKind : Set where
  repositoryKind : SymbolKind
  moduleKind : SymbolKind
  recordKind : SymbolKind
  dataKind : SymbolKind
  constructorKind : SymbolKind
  fieldKind : SymbolKind
  functionKind : SymbolKind
  theoremKind : SymbolKind
  postulateKind : SymbolKind
  binderKind : SymbolKind
  externalKind : SymbolKind

data EdgeKind : Set where
  containsEdge : EdgeKind
  importsEdge : EdgeKind
  opensEdge : EdgeKind
  typeDependsEdge : EdgeKind
  bodyDependsEdge : EdgeKind
  valueFlowsEdge : EdgeKind
  argumentToEdge : EdgeKind
  callsEdge : EdgeKind
  constructsEdge : EdgeKind
  fieldOfEdge : EdgeKind
  constructorOfEdge : EdgeKind
  bindsEdge : EdgeKind
  instantiatesEdge : EdgeKind
  rewritesWithEdge : EdgeKind
  patternMatchesEdge : EdgeKind

record SymbolNode : Set where
  constructor symbolNode
  field
    symbolId : String
    symbolLabel : String
    symbolKind : SymbolKind

    -- Empty/global scopes and declaration-local scopes are represented by
    -- stable strings at this abstract layer.  Concrete extractors may use a
    -- declaration identity here so equal binder spellings remain distinct.
    symbolScope : String

open SymbolNode public

record SemanticEdge : Set where
  constructor semanticEdge
  field
    edgeSource : String
    edgeTarget : String
    edgeKind : EdgeKind

open SemanticEdge public

record SemanticGraph : Set where
  constructor semanticGraph
  field
    graphNodes : List SymbolNode
    graphEdges : List SemanticEdge

open SemanticGraph public

------------------------------------------------------------------------
-- A graph delta is descriptive rather than renderer-owned.  A concrete
-- backend may animate the same delta using Manim, SVG, WebGPU, terminal
-- output, or any later frontend.
------------------------------------------------------------------------

data GraphDelta : Set where
  addNode : SymbolNode → GraphDelta
  removeNode : String → GraphDelta
  addEdge : SemanticEdge → GraphDelta
  removeEdge : SemanticEdge → GraphDelta
  renameNode : String → String → GraphDelta
  replaceGraph : SemanticGraph → GraphDelta

data DeltaIntent : Set where
  nodeAppears : DeltaIntent
  nodeDisappears : DeltaIntent
  edgeAppears : DeltaIntent
  edgeDisappears : DeltaIntent
  nodeIdentityChanges : DeltaIntent
  graphStateChanges : DeltaIntent

deltaIntent : GraphDelta → DeltaIntent
deltaIntent (addNode _) = nodeAppears
deltaIntent (removeNode _) = nodeDisappears
deltaIntent (addEdge _) = edgeAppears
deltaIntent (removeEdge _) = edgeDisappears
deltaIntent (renameNode _ _) = nodeIdentityChanges
deltaIntent (replaceGraph _) = graphStateChanges

------------------------------------------------------------------------
-- Smallest backend-independent animation vocabulary.
------------------------------------------------------------------------

data VisualPrimitive : Set where
  growNode : SymbolNode → VisualPrimitive
  fadeNode : String → VisualPrimitive
  growEdge : SemanticEdge → VisualPrimitive
  fadeEdge : SemanticEdge → VisualPrimitive
  morphNode : String → String → VisualPrimitive
  replaceSceneGraph : SemanticGraph → VisualPrimitive

primitiveIntent : VisualPrimitive → DeltaIntent
primitiveIntent (growNode _) = nodeAppears
primitiveIntent (fadeNode _) = nodeDisappears
primitiveIntent (growEdge _) = edgeAppears
primitiveIntent (fadeEdge _) = edgeDisappears
primitiveIntent (morphNode _ _) = nodeIdentityChanges
primitiveIntent (replaceSceneGraph _) = graphStateChanges

compileDelta : GraphDelta → VisualPrimitive
compileDelta (addNode node) = growNode node
compileDelta (removeNode nodeId) = fadeNode nodeId
compileDelta (addEdge edge) = growEdge edge
compileDelta (removeEdge edge) = fadeEdge edge
compileDelta (renameNode from to) = morphNode from to
compileDelta (replaceGraph graph) = replaceSceneGraph graph

compileDeltaIntentExact :
  ∀ delta →
  primitiveIntent (compileDelta delta) ≡ deltaIntent delta
compileDeltaIntentExact (addNode _) = refl
compileDeltaIntentExact (removeNode _) = refl
compileDeltaIntentExact (addEdge _) = refl
compileDeltaIntentExact (removeEdge _) = refl
compileDeltaIntentExact (renameNode _ _) = refl
compileDeltaIntentExact (replaceGraph _) = refl

------------------------------------------------------------------------
-- Explicit non-authority boundary for renderers.
------------------------------------------------------------------------

record TemporalSemanticGraphBoundary : Set where
  constructor temporalSemanticGraphBoundary
  field
    rendererOwnsSemanticIdentity : Bool
    rendererOwnsSemanticIdentityIsFalse :
      rendererOwnsSemanticIdentity ≡ false

    pixelEqualityDefinesGraphEquality : Bool
    pixelEqualityDefinesGraphEqualityIsFalse :
      pixelEqualityDefinesGraphEquality ≡ false

    layoutPositionDefinesNodeIdentity : Bool
    layoutPositionDefinesNodeIdentityIsFalse :
      layoutPositionDefinesNodeIdentity ≡ false

canonicalTemporalSemanticGraphBoundary : TemporalSemanticGraphBoundary
canonicalTemporalSemanticGraphBoundary =
  temporalSemanticGraphBoundary
    false refl
    false refl
    false refl
