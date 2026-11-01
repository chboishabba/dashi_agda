module DASHI.Foundations.Base369Ternary27StratifiedAppraisalFibreExact where

------------------------------------------------------------------------
-- STRATIFIED APPRAISAL FIBRES OVER THE BASE369 INTERACTION VOXEL
--
-- The 19683-state hyperfabric is a literal 729-point appraisal fibre over
-- each of the 27 interaction-base points.  This owner lifts the existing
-- centre/face/edge/corner stratification of the interaction voxel through
-- that projection without collapsing base stratum and fibre coordinates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Stratification

------------------------------------------------------------------------
-- 1. Fibre indexed by an exact interaction-base point.
------------------------------------------------------------------------

record AppraisalFibreOver (base : Geometry.Ternary27Point) : Set where
  constructor appraisalFibreOver
  field
    fibrePoint : Geometry.AppraisalFibrePoint
open AppraisalFibreOver public

assembleOver :
  (base : Geometry.Ternary27Point) →
  AppraisalFibreOver base →
  Geometry.TernaryHyperformalPoint
assembleOver base (appraisalFibreOver fibre) =
  Geometry.rebuildOverInteraction base fibre

assembleProjectsToBase :
  (base : Geometry.Ternary27Point) →
  (fibre : AppraisalFibreOver base) →
  Geometry.projectInteractionVoxel (assembleOver base fibre) ≡ base
assembleProjectsToBase base fibre = refl

assembleProjectsToFibre :
  (base : Geometry.Ternary27Point) →
  (fibre : AppraisalFibreOver base) →
  Geometry.projectAppraisalFibre (assembleOver base fibre) ≡ fibrePoint fibre
assembleProjectsToFibre base (appraisalFibreOver fibre) = refl

------------------------------------------------------------------------
-- 2. A fibre point whose base is known only up to a geometric stratum.
------------------------------------------------------------------------

record StratifiedAppraisalFibrePoint (s : Stratification.VoxelStratum) : Set where
  constructor stratifiedAppraisalFibrePoint
  field
    basePoint : Geometry.Ternary27Point
    baseHasStratum : Stratification.voxelStratum basePoint ≡ s
    appraisalPoint : Geometry.AppraisalFibrePoint
open StratifiedAppraisalFibrePoint public

forgetStratifiedFibre :
  ∀ {s} → StratifiedAppraisalFibrePoint s → Geometry.TernaryHyperformalPoint
forgetStratifiedFibre p =
  Geometry.rebuildOverInteraction (basePoint p) (appraisalPoint p)

forgetPreservesExactBase :
  ∀ {s} → (p : StratifiedAppraisalFibrePoint s) →
  Geometry.projectInteractionVoxel (forgetStratifiedFibre p) ≡ basePoint p
forgetPreservesExactBase p = refl

forgetPreservesBaseStratum :
  ∀ {s} → (p : StratifiedAppraisalFibrePoint s) →
  Stratification.voxelStratum
    (Geometry.projectInteractionVoxel (forgetStratifiedFibre p)) ≡ s
forgetPreservesBaseStratum p = baseHasStratum p

------------------------------------------------------------------------
-- 3. Exact lifted stratum cardinalities.
--
-- Each interaction point carries the same 729-point appraisal fibre.
------------------------------------------------------------------------

appraisalFibreCardinality : Nat
appraisalFibreCardinality = Geometry.appraisalFibreStateCount

centreFibreStateCount : Nat
centreFibreStateCount =
  Stratification.centreCount * appraisalFibreCardinality

faceCentreFibreStateCount : Nat
faceCentreFibreStateCount =
  Stratification.faceCentreCount * appraisalFibreCardinality

edgeCentreFibreStateCount : Nat
edgeCentreFibreStateCount =
  Stratification.edgeCentreCount * appraisalFibreCardinality

cornerFibreStateCount : Nat
cornerFibreStateCount =
  Stratification.cornerCount * appraisalFibreCardinality

centreFibreStateCountIs729 : centreFibreStateCount ≡ 729
centreFibreStateCountIs729 = refl

faceCentreFibreStateCountIs4374 : faceCentreFibreStateCount ≡ 4374
faceCentreFibreStateCountIs4374 = refl

edgeCentreFibreStateCountIs8748 : edgeCentreFibreStateCount ≡ 8748
edgeCentreFibreStateCountIs8748 = refl

cornerFibreStateCountIs5832 : cornerFibreStateCount ≡ 5832
cornerFibreStateCountIs5832 = refl

stratifiedFabricStateCount : Nat
stratifiedFabricStateCount =
  centreFibreStateCount
  + faceCentreFibreStateCount
  + edgeCentreFibreStateCount
  + cornerFibreStateCount

stratifiedFabricStateCountIs19683 : stratifiedFabricStateCount ≡ 19683
stratifiedFabricStateCountIs19683 = refl

stratifiedFabricCountAgreesWithGeometry :
  stratifiedFabricStateCount ≡ Geometry.hyperfabricStateCount
stratifiedFabricCountAgreesWithGeometry = refl

------------------------------------------------------------------------
-- 4. Product stratification keeps base and the two appraisal strata separate.
------------------------------------------------------------------------

record FullyStratifiedFabricPoint : Set where
  constructor fullyStratifiedFabricPoint
  field
    point : Geometry.TernaryHyperformalPoint
    interactionLayer : Stratification.VoxelStratum
    appraisalALayer : Stratification.VoxelStratum
    appraisalBLayer : Stratification.VoxelStratum
    interactionLayerExact :
      Stratification.voxelStratum (Geometry.interactionVoxel point) ≡ interactionLayer
    appraisalALayerExact :
      Stratification.voxelStratum (Geometry.appraisalAVoxel point) ≡ appraisalALayer
    appraisalBLayerExact :
      Stratification.voxelStratum (Geometry.appraisalBVoxel point) ≡ appraisalBLayer
open FullyStratifiedFabricPoint public

classifyFabricPoint : Geometry.TernaryHyperformalPoint → FullyStratifiedFabricPoint
classifyFabricPoint p =
  fullyStratifiedFabricPoint
    p
    (Stratification.voxelStratum (Geometry.interactionVoxel p))
    (Stratification.voxelStratum (Geometry.appraisalAVoxel p))
    (Stratification.voxelStratum (Geometry.appraisalBVoxel p))
    refl refl refl

------------------------------------------------------------------------
-- 5. Boundary: stratum information does not replace fibre information.
------------------------------------------------------------------------

record StratifiedAppraisalFibreBoundary : Set where
  constructor stratifiedAppraisalFibreBoundary
  field
    fibreCardinalityIs729 : Bool
    baseStrataLiftUniformlyThroughFibre : Bool
    liftedStrataSumTo19683 : Bool
    exactBaseRetainedInsideStratifiedFibre : Bool
    appraisalCoordinatesRetainedInsideStratifiedFibre : Bool
    interactionStratumDeterminesAppraisalCoordinates : Bool
    equalBaseStratumImpliesEqualBasePoint : Bool

canonicalStratifiedAppraisalFibreBoundary : StratifiedAppraisalFibreBoundary
canonicalStratifiedAppraisalFibreBoundary =
  stratifiedAppraisalFibreBoundary true true true true true false false
