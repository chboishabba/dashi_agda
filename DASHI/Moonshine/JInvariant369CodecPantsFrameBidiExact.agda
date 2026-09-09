module DASHI.Moonshine.JInvariant369CodecPantsFrameBidiExact where

------------------------------------------------------------------------
-- COMPACT 27 CODEC <-> PANTS FRAME BIDI
--
-- The generic CS 27 codec deliberately leaves the semantic meaning of its
-- framing trit open.  In the formulaic j renderer, however, the compact code
-- and the depth-3 pants path are both computed from the same Ternary27Point.
-- Therefore the third codec trit is exactly the third pants/refinement
-- coordinate for this consumer.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Moonshine.JInvariant369CodecReconciliationFrontierExact as Compact
import DASHI.Moonshine.JInvariantColourWheelNineSheetPantsGluingExact as PantsBridge
import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Moonshine.JInvariantFormulaic369FibreObserverRepairExact as Repair
import DASHI.Moonshine.JInvariantFormulaic369CompactCodecBidiExact as SamePoint
import DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact as Klein
import DASHI.Topology.TernaryCylinderPantsGeometryExact as Pants
import DASHI.Topology.TernaryPantsFrontierExact as Frontier

------------------------------------------------------------------------
-- 1. Complete the total 27 codec equivalence in the reverse direction.
------------------------------------------------------------------------

encodeDecodeCompact27 :
  (code : Compact.Compact27) →
  Compact.encodeCompact27 (Compact.decodeCompact27 code) ≡ code
encodeDecodeCompact27 (Compact.compact27 payload frame)
  rewrite Compact.encodeDecodeCompactNine payload = refl

------------------------------------------------------------------------
-- 2. The explicit frame trit and the third pants branch are the same finite
--    coordinate when both descend from one 27-point.
------------------------------------------------------------------------

frameToPantsSlot : SSP.SSPTrit → Pants.BranchSlot
frameToPantsSlot t = PantsBridge.kernelToSlot (Compact.sspToKernel t)

thirdPantsSlot : Frontier.PantsPath 3 → Pants.BranchSlot
thirdPantsSlot (a vcons b vcons c vcons vnil) = c

encodedFrameIsThirdPantsSlot :
  (p : Fabric.Ternary27Point) →
  frameToPantsSlot (Compact.frame3 (Compact.encodeCompact27 p))
  ≡ thirdPantsSlot (PantsBridge.voxel27ToPants3 p)
encodedFrameIsThirdPantsSlot (Fabric.ternary27Point x y z) = refl

------------------------------------------------------------------------
-- 3. Same-point renderer specialization.
------------------------------------------------------------------------

samePointCodecFrameIsPantsContinuation :
  (R : Render.JPhaseRenderingAlgebra) →
  (F : Repair.SamePointFibreObservers R) →
  (z : Klein.Point (Render.klein R)) →
  frameToPantsSlot
    (Compact.frame3 (SamePoint.code27 (SamePoint.encodeCompactAt R F z)))
  ≡ thirdPantsSlot
      (PantsBridge.voxel27ToPants3 (Repair.observer27At F z))
samePointCodecFrameIsPantsContinuation R F z =
  encodedFrameIsThirdPantsSlot (Repair.observer27At F z)

------------------------------------------------------------------------
-- 4. Boundary.
------------------------------------------------------------------------

record JInvariant369CodecPantsFrameBoundary : Set where
  constructor j-invariant-369-codec-pants-frame-boundary
  field
    compact27RoundTripsBothWays : Bool
    frameIsSamePointThirdPantsCoordinate : Bool
    frameIsIndependentOfContinuousPhase : Bool
    frameAutomaticallyEqualsAnalyticOpenClosedSeam : Bool
    frameAutomaticallyEqualsSmoothPantsSurfaceGeometry : Bool

canonicalJInvariant369CodecPantsFrameBoundary :
  JInvariant369CodecPantsFrameBoundary
canonicalJInvariant369CodecPantsFrameBoundary =
  j-invariant-369-codec-pants-frame-boundary
    true true true false false
