module DASHI.Visual.LayoutComplexityBoundaryExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- LAYOUT COMPLEXITY BOUNDARY
--
-- Small focused graphs may use an iterative force refinement. Large graphs use
-- a bounded deterministic placement preserving existing positions and placing
-- new nodes from semantic-neighbour anchors or a fallback grid.
------------------------------------------------------------------------

data LayoutRegime : Set where
  boundedSpringRegime : LayoutRegime
  deterministicLargeGraphRegime : LayoutRegime

record LayoutThreshold : Set where
  constructor layoutThreshold
  field
    springNodeLimit : Nat
    springEdgeLimit : Nat

open LayoutThreshold public

canonicalLayoutThreshold : LayoutThreshold
canonicalLayoutThreshold =
  layoutThreshold 180 600

data LayoutAdmission : Set where
  springLayoutAdmitted : LayoutAdmission
  springLayoutRejected : LayoutAdmission

largeGraphSpringAdmission : LayoutAdmission
largeGraphSpringAdmission = springLayoutRejected

largeGraphSpringIsRejected :
  largeGraphSpringAdmission ≡ springLayoutRejected
largeGraphSpringIsRejected = refl

record LayoutComplexityBoundary : Set where
  constructor layoutComplexityBoundary
  field
    largeGraphMayInvokeUnboundedForceSolve : Bool
    largeGraphMayInvokeUnboundedForceSolveIsFalse :
      largeGraphMayInvokeUnboundedForceSolve ≡ false

    existingPositionsRemainPreferredInFallback : Bool
    existingPositionsRemainPreferredInFallbackIsTrue :
      existingPositionsRemainPreferredInFallback ≡ true

    layoutAlgorithmDefinesSemanticEdges : Bool
    layoutAlgorithmDefinesSemanticEdgesIsFalse :
      layoutAlgorithmDefinesSemanticEdges ≡ false

canonicalLayoutComplexityBoundary :
  LayoutComplexityBoundary
canonicalLayoutComplexityBoundary =
  layoutComplexityBoundary
    false refl
    true refl
    false refl
