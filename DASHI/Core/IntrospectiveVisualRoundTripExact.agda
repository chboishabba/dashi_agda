module DASHI.Core.IntrospectiveVisualRoundTripExact where

------------------------------------------------------------------------
-- INTROSPECTIVE VISUAL ROUND-TRIP
--
-- Method:
--   1. formalise a theory faithfully;
--   2. render a deliberately chosen visual encoding;
--   3. extract structure from that rendering through a vision observer;
--   4. reify the observed structure into a second proof assistant.
--
-- The exact theorem below proves only the declared finite render/observe/reify
-- contract.  A real OpenCV run is an empirical producer of VisionEdge values;
-- it is not promoted into proof authority.  The accompanying Python harness
-- generates such a receipt and emits a Lean model of the detected structure.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- 1. Faithful finite theory.
------------------------------------------------------------------------

data TheoryNode : Set where
  source projection fibre refinement : TheoryNode

data TheoryEdge : Set where
  source→projection
  source→fibre
  projection→refinement
  fibre→refinement : TheoryEdge

------------------------------------------------------------------------
-- 2. Visual encoding.
--
-- These constructors represent semantic drawing instructions, not pixels.
-- The executable harness instantiates them as four filled node discs and four
-- orthogonal line segments in a 320×320 raster.
------------------------------------------------------------------------

data VisualEdge : Set where
  horizontalTop
  verticalLeft
  verticalRight
  horizontalBottom : VisualEdge

renderEdge : TheoryEdge → VisualEdge
renderEdge source→projection = horizontalTop
renderEdge source→fibre = verticalLeft
renderEdge projection→refinement = verticalRight
renderEdge fibre→refinement = horizontalBottom

------------------------------------------------------------------------
-- 3. Vision observation.
------------------------------------------------------------------------

data VisionEdge : Set where
  sawSourceProjection
  sawSourceFibre
  sawProjectionRefinement
  sawFibreRefinement : VisionEdge

idealVision : VisualEdge → VisionEdge
idealVision horizontalTop = sawSourceProjection
idealVision verticalLeft = sawSourceFibre
idealVision verticalRight = sawProjectionRefinement
idealVision horizontalBottom = sawFibreRefinement

recoverTheory : VisionEdge → TheoryEdge
recoverTheory sawSourceProjection = source→projection
recoverTheory sawSourceFibre = source→fibre
recoverTheory sawProjectionRefinement = projection→refinement
recoverTheory sawFibreRefinement = fibre→refinement

renderVisionRoundTrip :
  (edge : TheoryEdge) → recoverTheory (idealVision (renderEdge edge)) ≡ edge
renderVisionRoundTrip source→projection = refl
renderVisionRoundTrip source→fibre = refl
renderVisionRoundTrip projection→refinement = refl
renderVisionRoundTrip fibre→refinement = refl

------------------------------------------------------------------------
-- 4. Lean-facing reification.
------------------------------------------------------------------------

data LeanEdgeModel : Set where
  leanSourceProjection
  leanSourceFibre
  leanProjectionRefinement
  leanFibreRefinement : LeanEdgeModel

reifyLean : VisionEdge → LeanEdgeModel
reifyLean sawSourceProjection = leanSourceProjection
reifyLean sawSourceFibre = leanSourceFibre
reifyLean sawProjectionRefinement = leanProjectionRefinement
reifyLean sawFibreRefinement = leanFibreRefinement

reopenLean : LeanEdgeModel → VisionEdge
reopenLean leanSourceProjection = sawSourceProjection
reopenLean leanSourceFibre = sawSourceFibre
reopenLean leanProjectionRefinement = sawProjectionRefinement
reopenLean leanFibreRefinement = sawFibreRefinement

leanReificationRoundTrip :
  (seen : VisionEdge) → reopenLean (reifyLean seen) ≡ seen
leanReificationRoundTrip sawSourceProjection = refl
leanReificationRoundTrip sawSourceFibre = refl
leanReificationRoundTrip sawProjectionRefinement = refl
leanReificationRoundTrip sawFibreRefinement = refl

fullIntrospectiveRoundTrip :
  (edge : TheoryEdge) →
  recoverTheory (reopenLean (reifyLean (idealVision (renderEdge edge)))) ≡ edge
fullIntrospectiveRoundTrip source→projection = refl
fullIntrospectiveRoundTrip source→fibre = refl
fullIntrospectiveRoundTrip projection→refinement = refl
fullIntrospectiveRoundTrip fibre→refinement = refl

------------------------------------------------------------------------
-- Contracts for non-ideal / empirical observers.
------------------------------------------------------------------------

record VisionObserverContract (observe : VisualEdge → VisionEdge) : Set where
  constructor visionObserverContract
  field
    soundForDeclaredEncoding :
      (edge : TheoryEdge) → recoverTheory (observe (renderEdge edge)) ≡ edge

open VisionObserverContract public

contractImpliesTheoryRecovery :
  (observe : VisualEdge → VisionEdge) →
  VisionObserverContract observe →
  (edge : TheoryEdge) →
  recoverTheory (observe (renderEdge edge)) ≡ edge
contractImpliesTheoryRecovery observe contract edge =
  soundForDeclaredEncoding contract edge

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record IntrospectiveMethodBoundary : Set where
  constructor introspectiveMethodBoundary
  field
    visualisationAloneProvesTheory : Bool
    opencvReceiptAloneProvesSemanticFaithfulness : Bool
    leanReificationAloneProvesVisionCorrectness : Bool
    provedRenderObserverContractClosesFiniteRoundTrip : Bool
    empiricalVisionCanSupplyAReifiableObservation : Bool

canonicalIntrospectiveMethodBoundary : IntrospectiveMethodBoundary
canonicalIntrospectiveMethodBoundary =
  introspectiveMethodBoundary false false false true true

introspectiveMethodStatement : String
introspectiveMethodStatement =
  "Formalise first, render second, inspect the rendering with an independent observer, then reify the observed structure in a second prover. The visual/CV stage is an empirical producer unless separately covered by a proved extraction contract; successful round-trip agreement is evidence and a regression oracle, not automatic semantic proof."
