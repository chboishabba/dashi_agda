module DASHI.Visual.RootedSemanticFocusExact where

open import DASHI.Core.Prelude
open import DASHI.Core.TemporalSemanticGraphExact

------------------------------------------------------------------------
-- ROOTED SEMANTIC FOCUS
--
-- A focused view selects an existing root and expands through existing
-- semantic relations.  It is a projection of the authority graph, never a
-- source of new semantic nodes or edges.
------------------------------------------------------------------------

data TraversalDirection : Set where
  upstreamDependencies : TraversalDirection
  downstreamConsumers : TraversalDirection

data FocusStepKind : Set where
  rootStep : FocusStepKind
  upstreamStep : FocusStepKind
  downstreamStep : FocusStepKind

record FocusStep : Set where
  constructor focusStep
  field
    focusStepNodeId : String
    focusStepKind : FocusStepKind
    focusStepDepth : Nat

open FocusStep public

record RootedSemanticFocus : Set where
  constructor rootedSemanticFocus
  field
    focusRootId : String
    focusSteps : List FocusStep
    focusEdgeIds : List String

open RootedSemanticFocus public

data FocusVisualPrimitive : Set where
  revealFocusRoot : String → FocusVisualPrimitive
  revealFocusLayer : Nat → FocusVisualPrimitive
  revealFocusEdges : List String → FocusVisualPrimitive

data FocusVisualIntent : Set where
  focusRootAppears : FocusVisualIntent
  focusLayerAppears : FocusVisualIntent
  focusRelationsAppear : FocusVisualIntent

focusVisualIntent : FocusVisualPrimitive → FocusVisualIntent
focusVisualIntent (revealFocusRoot _) = focusRootAppears
focusVisualIntent (revealFocusLayer _) = focusLayerAppears
focusVisualIntent (revealFocusEdges _) = focusRelationsAppear

compileRootReveal :
  RootedSemanticFocus →
  FocusVisualPrimitive
compileRootReveal focus =
  revealFocusRoot (focusRootId focus)

compileRootRevealIntentExact :
  ∀ focus →
  focusVisualIntent (compileRootReveal focus)
    ≡ focusRootAppears
compileRootRevealIntentExact _ = refl

record RootedSemanticFocusBoundary : Set where
  constructor rootedSemanticFocusBoundary
  field
    focusMayInventNode : Bool
    focusMayInventNodeIsFalse :
      focusMayInventNode ≡ false

    focusMayInventEdge : Bool
    focusMayInventEdgeIsFalse :
      focusMayInventEdge ≡ false

    upstreamMayReverseSemanticEdgeAuthority : Bool
    upstreamMayReverseSemanticEdgeAuthorityIsFalse :
      upstreamMayReverseSemanticEdgeAuthority ≡ false

    downstreamMayReverseSemanticEdgeAuthority : Bool
    downstreamMayReverseSemanticEdgeAuthorityIsFalse :
      downstreamMayReverseSemanticEdgeAuthority ≡ false

    focusLayoutDefinesSemanticReachability : Bool
    focusLayoutDefinesSemanticReachabilityIsFalse :
      focusLayoutDefinesSemanticReachability ≡ false

canonicalRootedSemanticFocusBoundary :
  RootedSemanticFocusBoundary
canonicalRootedSemanticFocusBoundary =
  rootedSemanticFocusBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
