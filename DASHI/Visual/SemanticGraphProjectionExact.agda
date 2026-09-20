module DASHI.Visual.SemanticGraphProjectionExact where

open import DASHI.Core.Prelude
open import DASHI.Core.TemporalSemanticGraphExact

------------------------------------------------------------------------
-- SEMANTIC GRAPH -> SIMPLE VISUAL GRAPH PROJECTION
--
-- Manim DiGraph is a simple directed graph keyed by endpoint pairs.  The
-- semantic authority graph can contain several typed relations with the same
-- endpoints.  A visual backend may quotient those geometric edges only when
-- the typed semantic relations remain available as authority data.
------------------------------------------------------------------------

data VisualEdgeProjectionPolicy : Set where
  preserveTypedRelations : VisualEdgeProjectionPolicy
  quotientByEndpointPair : VisualEdgeProjectionPolicy

record VisualEdgeProjectionReceipt : Set where
  constructor visualEdgeProjectionReceipt
  field
    projectionPolicy : VisualEdgeProjectionPolicy

    semanticRelationsRemainAuthoritative : Bool
    semanticRelationsRemainAuthoritativeIsTrue :
      semanticRelationsRemainAuthoritative ≡ true

    visualEdgeMultiplicityDefinesSemanticMultiplicity : Bool
    visualEdgeMultiplicityDefinesSemanticMultiplicityIsFalse :
      visualEdgeMultiplicityDefinesSemanticMultiplicity ≡ false

open VisualEdgeProjectionReceipt public

canonicalManimSimpleGraphProjection :
  VisualEdgeProjectionReceipt
canonicalManimSimpleGraphProjection =
  visualEdgeProjectionReceipt
    quotientByEndpointPair
    true refl
    false refl

record SemanticGraphProjectionBoundary : Set where
  constructor semanticGraphProjectionBoundary
  field
    quotientMayDeleteSemanticEvidence : Bool
    quotientMayDeleteSemanticEvidenceIsFalse :
      quotientMayDeleteSemanticEvidence ≡ false

    rendererProjectionMayBecomeAuthorityGraph : Bool
    rendererProjectionMayBecomeAuthorityGraphIsFalse :
      rendererProjectionMayBecomeAuthorityGraph ≡ false

canonicalSemanticGraphProjectionBoundary :
  SemanticGraphProjectionBoundary
canonicalSemanticGraphProjectionBoundary =
  semanticGraphProjectionBoundary
    false refl
    false refl
