module DASHI.Physics.Closure.NSTriadKNProfileCrossWeightBridge where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.Closure.NSTriadKNProfileCrossForcedTailRefinement public
import DASHI.Physics.Closure.NSTriadKNProfileCrossWeightModel as WeightModel
import DASHI.Physics.Closure.NSTriadKNAdversarialColumnClosureDependency as AdversarialColumn
import DASHI.Physics.Closure.NSTriadKNTransitionClosureDependency as TransitionClosure

------------------------------------------------------------------------
-- Weight-model bridge for the forced-tail off-diagonal profile route.
--
-- The refinement surface defines the theorem shapes and keeps its
-- "canonical" placeholders postulated to avoid an import cycle.
-- This bridge is the non-cyclic instantiation point:
--
--   WeightModel  ->  weight orientation gain witnesses
--   Refinement   ->  restricted-row / cross-product record shapes
--
-- So downstream modules can depend on actual terms rather than the
-- refinement module's documentary placeholders.
--
-- On the active dependency path this bridge is the Blocker 1 discharge
-- point: the FT→adv / FT→trans restricted-row and special cross terms are
-- built from WeightModel's depth-bearing profile labels, not from the
-- refinement module's postulated placeholder canonicals.

ftAdvWeightGainFromDepthGeometry :
  ForcedTailAdversarialWeightOrientationGain
ftAdvWeightGainFromDepthGeometry =
  WeightModel.canonicalFTAdvWeightOrientationGain

ftTransWeightGainFromDepthGeometry :
  ForcedTailTransitionWeightOrientationGain
ftTransWeightGainFromDepthGeometry =
  WeightModel.canonicalFTTransWeightOrientationGain

ftAdvRowN1FromDepthGeometry :
  ForcedTailToAdversarialRestrictedRowN1
ftAdvRowN1FromDepthGeometry =
  forcedTailToAdversarialRestrictedRowN1FromWeight
    ftAdvWeightGainFromDepthGeometry

ftTransRowN1FromDepthGeometry :
  ForcedTailToTransitionRestrictedRowN1
ftTransRowN1FromDepthGeometry =
  forcedTailToTransitionRestrictedRowN1FromWeight
    ftTransWeightGainFromDepthGeometry

ftAdvCrossFromDepthGeometry :
  ForcedTailAdversarialCrossProductN2
ftAdvCrossFromDepthGeometry =
  mkForcedTailAdversarialCrossProductN2
    ftAdvRowN1FromDepthGeometry
    AdversarialColumn.canonicalNSTriadKNAdversarialColumnClosureDependency

ftTransCrossFromDepthGeometry :
  ForcedTailTransitionCrossProductN2
ftTransCrossFromDepthGeometry =
  mkForcedTailTransitionCrossProductN2
    ftTransRowN1FromDepthGeometry
    TransitionClosure.canonicalNSTriadKNTransitionColumnClosureDependency

blocker1DepthRouteClosed : Bool
blocker1DepthRouteClosed = true

blocker1DepthRouteClosedIsTrue :
  blocker1DepthRouteClosed ≡ true
blocker1DepthRouteClosedIsTrue = refl

weightRouteStillConditional : Bool
weightRouteStillConditional = false
-- This remains false because the active downstream route no longer depends on
-- the refinement module's placeholder canonicals.  The remaining assumptions
-- live only in the shared depth-geometry base (for example `entryDepth` and
-- `forcedTailSourceDepthCap`), not in a label-soundness or restricted-row
-- placeholder layer.
