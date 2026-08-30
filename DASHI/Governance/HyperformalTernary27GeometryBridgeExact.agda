module DASHI.Governance.HyperformalTernary27GeometryBridgeExact where

------------------------------------------------------------------------
-- EPISTEMIC9 <-> SSPTrit^9 <-> (TERNARY27)^3
--
-- The existing carrier-equivalence theorem supplies the semantic-policy bridge
-- from EpistemicTrit^9 to SSPTrit^9.  The geometry owner supplies an exact
-- regrouping of SSPTrit^9 into three 3x3x3 cubes.  Their composition is an
-- actual geometric chart, not a semantic identification across domains.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Governance.HyperformalTernaryCarrierEquivalenceExact as Carrier
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369NineCoordinateAggregateBridgeExact as Aggregate

------------------------------------------------------------------------
-- 1. Exact chart maps.
------------------------------------------------------------------------

epistemic9ToHyperfabric : Carrier.Epistemic9 → Geometry.TernaryHyperformalPoint
epistemic9ToHyperfabric state =
  Geometry.nineTritsToFabric (Carrier.epistemic9ToNineTrits state)

hyperfabricToEpistemic9 : Geometry.TernaryHyperformalPoint → Carrier.Epistemic9
hyperfabricToEpistemic9 point =
  Carrier.nineTritsToEpistemic9 (Geometry.fabricToNineTrits point)

epistemicHyperfabricRoundTrip :
  (state : Carrier.Epistemic9) →
  hyperfabricToEpistemic9 (epistemic9ToHyperfabric state) ≡ state
epistemicHyperfabricRoundTrip state
  rewrite Geometry.fabricNineRoundTrip
    (Geometry.nineTritsToFabric (Carrier.epistemic9ToNineTrits state))
        | Carrier.epistemic9RoundTrip state = refl

hyperfabricEpistemicRoundTrip :
  (point : Geometry.TernaryHyperformalPoint) →
  epistemic9ToHyperfabric (hyperformalToEpistemic9 point) ≡ point
hyperfabricEpistemicRoundTrip point
  rewrite Carrier.nineTritsEpistemic9RoundTrip (Geometry.fabricToNineTrits point)
        | Geometry.fabricNineRoundTrip point = refl

------------------------------------------------------------------------
-- 2. Explicit cube projections of an epistemic nine-state.
------------------------------------------------------------------------

epistemicInteractionVoxel : Carrier.Epistemic9 → Geometry.Ternary27Point
epistemicInteractionVoxel state =
  Geometry.interactionVoxel (epistemic9ToHyperfabric state)

epistemicAppraisalAVoxel : Carrier.Epistemic9 → Geometry.Ternary27Point
epistemicAppraisalAVoxel state =
  Geometry.appraisalAVoxel (epistemic9ToHyperfabric state)

epistemicAppraisalBVoxel : Carrier.Epistemic9 → Geometry.Ternary27Point
epistemicAppraisalBVoxel state =
  Geometry.appraisalBVoxel (epistemic9ToHyperfabric state)

------------------------------------------------------------------------
-- 3. Geometry can be observed coarsely without recovering the full fabric.
------------------------------------------------------------------------

record InteractionVoxelObservation : Set where
  constructor interactionVoxelObservation
  field observedInteractionVoxel : Geometry.Ternary27Point
open InteractionVoxelObservation public

observeInteractionVoxel :
  Geometry.TernaryHyperformalPoint → InteractionVoxelObservation
observeInteractionVoxel point =
  interactionVoxelObservation (Geometry.projectInteractionVoxel point)

record SameInteractionDifferentFibreWitness : Set where
  constructor sameInteractionDifferentFibreWitness
  field
    interaction : Geometry.Ternary27Point
    fibreA : Geometry.AppraisalFibrePoint
    fibreB : Geometry.AppraisalFibrePoint

canonicalInteractionFibreSeparation : SameInteractionDifferentFibreWitness
canonicalInteractionFibreSeparation =
  sameInteractionDifferentFibreWitness
    Geometry.origin
    (Geometry.appraisalFibrePoint Geometry.origin Geometry.origin)
    (Geometry.appraisalFibrePoint Geometry.negativeCorner Geometry.positiveCorner)

sameObservedInteractionSurface :
  Geometry.projectInteractionVoxel
    (Geometry.rebuildOverInteraction
      Geometry.origin
      (Geometry.appraisalFibrePoint Geometry.origin Geometry.origin))
  ≡
  Geometry.projectInteractionVoxel
    (Geometry.rebuildOverInteraction
      Geometry.origin
      (Geometry.appraisalFibrePoint Geometry.negativeCorner Geometry.positiveCorner))
sameObservedInteractionSurface = refl

------------------------------------------------------------------------
-- 4. Local one-coordinate moves are literal hyperfabric edges.
------------------------------------------------------------------------

originToPositiveInteractionXIsFabricEdge :
  Geometry.HyperformalAdjacent
    Geometry.fabricOrigin
    Geometry.fabricOriginInteractionXNeighbour
originToPositiveInteractionXIsFabricEdge =
  Geometry.fabricOriginAdjacentAlongInteractionX

------------------------------------------------------------------------
-- 5. Boundary receipt.
------------------------------------------------------------------------

record HyperformalTernary27GeometryBoundary : Set where
  constructor hyperformalTernary27GeometryBoundary
  field
    epistemicNineHasExactHyperformalChart : Bool
    chartUsesThreeTwentySevenPointCubes : Bool
    hyperfabricHasNineteenThousandSixHundredEightyThreePoints : Bool
    interactionProjectionRecoversAppraisalFibre : Bool
    oneCoordinateStepIsFabricEdge : Bool
    negativeToPositiveIsOneGridStep : Bool
    geometryCreatesSemanticIdentityAcrossDomains : Bool

canonicalHyperformalTernary27GeometryBoundary : HyperformalTernary27GeometryBoundary
canonicalHyperformalTernary27GeometryBoundary =
  hyperformalTernary27GeometryBoundary
    true true true false true false false
