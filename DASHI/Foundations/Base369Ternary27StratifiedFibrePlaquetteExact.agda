module DASHI.Foundations.Base369Ternary27StratifiedFibrePlaquetteExact where

------------------------------------------------------------------------
-- EXACT UNIT PLAQUETTES IN THE NON-PERIODIC 3x3x3 TERNARY GRID
--
-- A plaquette is four actual nearest-neighbour edges in P3 □ P3 □ P3.
-- The same square can be lifted into appraisal-A or appraisal-B while the
-- interaction base is fixed, making its fibre location explicit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Stratification
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral
import DASHI.Moonshine.Base369Ternary27SignedSymmetryMonsterIntertwinerExact as Signed
import DASHI.Moonshine.Base369Ternary27CharacterAdjacencyEquivarianceExact as Character

------------------------------------------------------------------------
-- 1. Four-edge plaquette record.
------------------------------------------------------------------------

record Plaquette4 : Set where
  constructor plaquette4
  field
    v00 v10 v11 v01 : Geometry.Ternary27Point
    edge00to10 : Geometry.HypervoxelAdjacent v00 v10
    edge10to11 : Geometry.HypervoxelAdjacent v10 v11
    edge11to01 : Geometry.HypervoxelAdjacent v11 v01
    edge01to00 : Geometry.HypervoxelAdjacent v01 v00
open Plaquette4 public

------------------------------------------------------------------------
-- 2. Concrete lower-left xy plaquette in the z=0 slice.
------------------------------------------------------------------------

xy00 : Geometry.Ternary27Point
xy00 = Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero

xy10 : Geometry.Ternary27Point
xy10 = Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero

xy11 : Geometry.Ternary27Point
xy11 = Geometry.origin

xy01 : Geometry.Ternary27Point
xy01 = Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero

lowerXYPlaquette : Plaquette4
lowerXYPlaquette =
  plaquette4
    xy00 xy10 xy11 xy01
    (Geometry.adjacentX Geometry.negToZero)
    (Geometry.adjacentY Geometry.negToZero)
    (Geometry.adjacentX Geometry.zeroToNeg)
    (Geometry.adjacentY Geometry.zeroToNeg)

------------------------------------------------------------------------
-- 3. Exact stratum itinerary around this unit square.
------------------------------------------------------------------------

xy00IsEdgeCentre :
  Stratification.voxelStratum xy00 ≡ Stratification.edgeCentreStratum
xy00IsEdgeCentre = refl

xy10IsFaceCentre :
  Stratification.voxelStratum xy10 ≡ Stratification.faceCentreStratum
xy10IsFaceCentre = refl

xy11IsCentre :
  Stratification.voxelStratum xy11 ≡ Stratification.centreStratum
xy11IsCentre = refl

xy01IsFaceCentre :
  Stratification.voxelStratum xy01 ≡ Stratification.faceCentreStratum
xy01IsFaceCentre = refl

record PlaquetteStratumItinerary : Set where
  constructor plaquetteStratumItinerary
  field
    s00 s10 s11 s01 : Stratification.VoxelStratum
open PlaquetteStratumItinerary public

plaquetteStrata : Plaquette4 → PlaquetteStratumItinerary
plaquetteStrata p =
  plaquetteStratumItinerary
    (Stratification.voxelStratum (v00 p))
    (Stratification.voxelStratum (v10 p))
    (Stratification.voxelStratum (v11 p))
    (Stratification.voxelStratum (v01 p))

lowerXYStratumItinerary :
  plaquetteStrata lowerXYPlaquette ≡
  plaquetteStratumItinerary
    Stratification.edgeCentreStratum
    Stratification.faceCentreStratum
    Stratification.centreStratum
    Stratification.faceCentreStratum
lowerXYStratumItinerary = refl

------------------------------------------------------------------------
-- 4. Lift a voxel plaquette vertically into appraisal-A over a fixed base.
------------------------------------------------------------------------

record AppraisalAPlaquetteOver (base : Geometry.Ternary27Point) : Set where
  constructor appraisalAPlaquetteOver
  field
    underlyingPlaquette : Plaquette4
    fixedAppraisalB : Geometry.Ternary27Point
open AppraisalAPlaquetteOver public

liftA00 :
  (base : Geometry.Ternary27Point) → AppraisalAPlaquetteOver base →
  Geometry.TernaryHyperformalPoint
liftA00 base p =
  Geometry.ternaryHyperformalPoint base (v00 (underlyingPlaquette p)) (fixedAppraisalB p)

liftA10 :
  (base : Geometry.Ternary27Point) → AppraisalAPlaquetteOver base →
  Geometry.TernaryHyperformalPoint
liftA10 base p =
  Geometry.ternaryHyperformalPoint base (v10 (underlyingPlaquette p)) (fixedAppraisalB p)

liftA11 :
  (base : Geometry.Ternary27Point) → AppraisalAPlaquetteOver base →
  Geometry.TernaryHyperformalPoint
liftA11 base p =
  Geometry.ternaryHyperformalPoint base (v11 (underlyingPlaquette p)) (fixedAppraisalB p)

liftA01 :
  (base : Geometry.Ternary27Point) → AppraisalAPlaquetteOver base →
  Geometry.TernaryHyperformalPoint
liftA01 base p =
  Geometry.ternaryHyperformalPoint base (v01 (underlyingPlaquette p)) (fixedAppraisalB p)

liftedEdge00to10 :
  (base : Geometry.Ternary27Point) → (p : AppraisalAPlaquetteOver base) →
  Geometry.HyperformalAdjacent (liftA00 base p) (liftA10 base p)
liftedEdge00to10 base p =
  Geometry.appraisalAAdjacent (edge00to10 (underlyingPlaquette p))

liftedEdge10to11 :
  (base : Geometry.Ternary27Point) → (p : AppraisalAPlaquetteOver base) →
  Geometry.HyperformalAdjacent (liftA10 base p) (liftA11 base p)
liftedEdge10to11 base p =
  Geometry.appraisalAAdjacent (edge10to11 (underlyingPlaquette p))

liftedEdge11to01 :
  (base : Geometry.Ternary27Point) → (p : AppraisalAPlaquetteOver base) →
  Geometry.HyperformalAdjacent (liftA11 base p) (liftA01 base p)
liftedEdge11to01 base p =
  Geometry.appraisalAAdjacent (edge11to01 (underlyingPlaquette p))

liftedEdge01to00 :
  (base : Geometry.Ternary27Point) → (p : AppraisalAPlaquetteOver base) →
  Geometry.HyperformalAdjacent (liftA01 base p) (liftA00 base p)
liftedEdge01to00 base p =
  Geometry.appraisalAAdjacent (edge01to00 (underlyingPlaquette p))

originFibreLowerXY : AppraisalAPlaquetteOver Geometry.origin
originFibreLowerXY = appraisalAPlaquetteOver lowerXYPlaquette Geometry.origin

originFibrePlaquetteBasePinned00 :
  Geometry.projectInteractionVoxel (liftA00 Geometry.origin originFibreLowerXY)
  ≡ Geometry.origin
originFibrePlaquetteBasePinned00 = refl

originFibrePlaquetteBasePinned11 :
  Geometry.projectInteractionVoxel (liftA11 Geometry.origin originFibreLowerXY)
  ≡ Geometry.origin
originFibrePlaquetteBasePinned11 = refl

------------------------------------------------------------------------
-- 5. Exact symmetry transport of plaquettes.
------------------------------------------------------------------------

swapPlaquette : Plaquette4 → Plaquette4
swapPlaquette p =
  plaquette4
    (Spectral.swapXY (v00 p))
    (Spectral.swapXY (v10 p))
    (Spectral.swapXY (v11 p))
    (Spectral.swapXY (v01 p))
    (Character.swapPreservesAdjacency (edge00to10 p))
    (Character.swapPreservesAdjacency (edge10to11 p))
    (Character.swapPreservesAdjacency (edge11to01 p))
    (Character.swapPreservesAdjacency (edge01to00 p))

flipXPlaquette : Plaquette4 → Plaquette4
flipXPlaquette p =
  plaquette4
    (Signed.flipX (v00 p))
    (Signed.flipX (v10 p))
    (Signed.flipX (v11 p))
    (Signed.flipX (v01 p))
    (Signed.flipXPreservesAdjacency (edge00to10 p))
    (Signed.flipXPreservesAdjacency (edge10to11 p))
    (Signed.flipXPreservesAdjacency (edge11to01 p))
    (Signed.flipXPreservesAdjacency (edge01to00 p))

------------------------------------------------------------------------
-- 6. Boundary: an exact plaquette does not yet supply gauge curvature.
------------------------------------------------------------------------

record StratifiedFibrePlaquetteBoundary : Set where
  constructor stratifiedFibrePlaquetteBoundary
  field
    fourActualGridEdgesConstructed : Bool
    plaquetteStratumItineraryRetained : Bool
    plaquetteCanLiveInsideFixedAppraisalFibre : Bool
    coordinateSymmetriesTransportPlaquettes : Bool
    plaquetteIsPeriodicC3SquaredCell : Bool
    gaugeConnectionAssignedToEdges : Bool
    curvatureComputedFromPlaquette : Bool
    wilsonLoopComputed : Bool

canonicalStratifiedFibrePlaquetteBoundary : StratifiedFibrePlaquetteBoundary
canonicalStratifiedFibrePlaquetteBoundary =
  stratifiedFibrePlaquetteBoundary true true true true false false false false
