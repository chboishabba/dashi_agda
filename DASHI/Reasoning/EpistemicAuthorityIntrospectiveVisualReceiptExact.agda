module DASHI.Reasoning.EpistemicAuthorityIntrospectiveVisualReceiptExact where

------------------------------------------------------------------------
-- Introspective visualization receipt for folk-law epistemic authority.
--
-- Pipeline:
--   1. formal theory in FolkLawEpistemicAuthorityCaptureExact;
--   2. deterministic raster generated from the theory-shaped specimen;
--   3. OpenCV connected-component analysis over node/edge/terminal channels;
--   4. machine-observed structure reintroduced here as a finite formal model.
--
-- The interesting result is deliberately not "the picture agrees perfectly".
-- The semantic graph has five directed edges, but the raster has only four
-- connected edge components: the two outgoing branch strokes from `received`
-- touch at their common branch origin and become one visual component.
-- Thus the visualization itself introduces a quotient/fibre collision.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.ObserverRefinementLatticeExact as Observer
open import DASHI.Reasoning.FolkLawEpistemicAuthorityCaptureExact

------------------------------------------------------------------------
-- Machine receipt counts
------------------------------------------------------------------------

record VisionReceipt : Set where
  constructor visionReceipt
  field
    semanticNodeCount            : Nat
    detectedNodeComponentCount   : Nat
    semanticEdgeCount            : Nat
    detectedEdgeComponentCount   : Nat
    detectedTerminalMarkerCount  : Nat
    semanticBranchOriginCount    : Nat

open VisionReceipt public

opencvAuthorityReceipt : VisionReceipt
opencvAuthorityReceipt = visionReceipt 6 6 5 4 2 1

nodesRecoveredExactly :
  detectedNodeComponentCount opencvAuthorityReceipt ≡
  semanticNodeCount opencvAuthorityReceipt
nodesRecoveredExactly = refl

oneSemanticEdgeDistinctionLostInConnectedComponents :
  semanticEdgeCount opencvAuthorityReceipt ≡
  suc (detectedEdgeComponentCount opencvAuthorityReceipt)
oneSemanticEdgeDistinctionLostInConnectedComponents = refl

twoTerminalMarkersDetected :
  detectedTerminalMarkerCount opencvAuthorityReceipt ≡ 2
twoTerminalMarkersDetected = refl

oneSharedBranchOrigin :
  semanticBranchOriginCount opencvAuthorityReceipt ≡ 1
oneSharedBranchOrigin = refl

------------------------------------------------------------------------
-- Semantic edge set and the pixel connected-component observer recovered by
-- OpenCV.  Two semantically distinct outgoing edges collapse visually.
------------------------------------------------------------------------

data SemanticEdge : Set where
  receivedToApparent       : SemanticEdge
  apparentToPersisted      : SemanticEdge
  persistedToObjective     : SemanticEdge
  receivedToComprehended   : SemanticEdge
  comprehendedToWithdraw   : SemanticEdge

data PixelEdgeComponent : Set where
  sharedReceivedBranchComponent : PixelEdgeComponent
  apparentPersistComponent      : PixelEdgeComponent
  persistObjectiveComponent     : PixelEdgeComponent
  comprehendWithdrawComponent   : PixelEdgeComponent

pixelEdgeObserver : Observer.Observer SemanticEdge PixelEdgeComponent
pixelEdgeObserver receivedToApparent       = sharedReceivedBranchComponent
pixelEdgeObserver apparentToPersisted      = apparentPersistComponent
pixelEdgeObserver persistedToObjective     = persistObjectiveComponent
pixelEdgeObserver receivedToComprehended   = sharedReceivedBranchComponent
pixelEdgeObserver comprehendedToWithdraw   = comprehendWithdrawComponent

semanticBranchEdgesDistinct :
  receivedToApparent ≡ receivedToComprehended → ⊥
semanticBranchEdgesDistinct ()

pixelBranchCollision : Observer.ObserverCollision pixelEdgeObserver
pixelBranchCollision =
  Observer.observerCollision
    receivedToApparent
    receivedToComprehended
    refl
    semanticBranchEdgesDistinct

pixelEdgeObserverNotSeparating :
  Observer.Separating pixelEdgeObserver → ⊥
pixelEdgeObserverNotSeparating =
  Observer.collisionBlocksSeparation pixelBranchCollision

------------------------------------------------------------------------
-- A refined edge observer restores semantic identity.  This is the formal
-- feedback step from image analysis back into the model: the next visualizer
-- should assign branch-local identity (e.g. separated geometry or a dedicated
-- channel) rather than relying only on connected components.
------------------------------------------------------------------------

semanticEdgeObserver : Observer.Observer SemanticEdge SemanticEdge
semanticEdgeObserver edge = edge

semanticEdgeObserverSeparating : Observer.Separating semanticEdgeObserver
semanticEdgeObserverSeparating x y equality = equality

pixelObserverRefinedBySemanticIdentity :
  Observer.Refines pixelEdgeObserver semanticEdgeObserver
pixelObserverRefinedBySemanticIdentity x y refl = refl

pixelToSemanticStrictRefinement :
  Observer.StrictRefinement pixelEdgeObserver semanticEdgeObserver
pixelToSemanticStrictRefinement =
  Observer.strictRefinement
    pixelObserverRefinedBySemanticIdentity
    receivedToApparent
    receivedToComprehended
    refl
    semanticBranchEdgesDistinct

------------------------------------------------------------------------
-- The introspective method itself as a small boundary receipt.
------------------------------------------------------------------------

record IntrospectiveMethodBoundary : Set where
  constructor introspectiveMethodBoundary
  field
    theoryModelledBeforeVisualization : Bool
    theoryModelledBeforeVisualizationIsTrue :
      theoryModelledBeforeVisualization ≡ true
    visualizationMachineRead : Bool
    visualizationMachineReadIsTrue : visualizationMachineRead ≡ true
    visualObserverCanIntroduceNewCollision : Bool
    visualObserverCanIntroduceNewCollisionIsTrue :
      visualObserverCanIntroduceNewCollision ≡ true
    analysisFeedsObserverRefinement : Bool
    analysisFeedsObserverRefinementIsTrue :
      analysisFeedsObserverRefinement ≡ true
    pixelsAloneGrantSemanticAuthority : Bool
    pixelsAloneGrantSemanticAuthorityIsFalse :
      pixelsAloneGrantSemanticAuthority ≡ false

canonicalIntrospectiveMethodBoundary : IntrospectiveMethodBoundary
canonicalIntrospectiveMethodBoundary =
  introspectiveMethodBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
