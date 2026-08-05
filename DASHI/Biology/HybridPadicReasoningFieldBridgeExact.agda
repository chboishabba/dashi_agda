module DASHI.Biology.HybridPadicReasoningFieldBridgeExact where

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Geometry.SSP369Ultrametric as U369
import DASHI.Biology.HallHybridManifoldTreeCarrier as Hall
import DASHI.Biology.PadicCylinderLODReasoningField as LOD

------------------------------------------------------------------------
-- Cross-pollination with the existing Round Three hybrid manifold/tree carrier.
--
-- The first two ternary digits retain the existing ultrametric branch address.
-- A third digit records the local chart coordinate.  The result is an exact
-- finite observation bridge into the Round Four depth-three voxel layout.
-- It does not identify chart geometry with tree geometry: each occupies its
-- own coordinate in the combined address.

chartDigit : Hall.LocalChartPoint → U369.Digit369
chartDigit Hall.chartPoint0 = U369.digit3
chartDigit Hall.chartPoint1 = U369.digit6
chartDigit Hall.chartPoint2 = U369.digit9

hybridAddress3 : Hall.HybridVisualPoint → LOD.DepthThreeAddress
hybridAddress3
  (Hall.hybridVisualPoint (a vcons b vcons vnil) chart) =
  a vcons b vcons chartDigit chart vcons vnil

hybridVoxel3 : Hall.HybridVisualPoint → LOD.Voxel3
hybridVoxel3 point = LOD.embedDepthThree (hybridAddress3 point)

habitualOriginVoxel :
  hybridVoxel3 Hall.habitualChartOrigin ≡ LOD.voxel3 0 0 0
habitualOriginVoxel = refl

habitualNeighbourVoxel :
  hybridVoxel3 Hall.habitualChartNeighbour ≡ LOD.voxel3 0 0 1
habitualNeighbourVoxel = refl

nearbyBranchVoxel :
  hybridVoxel3 Hall.nearbyBranchOrigin ≡ LOD.voxel3 0 1 0
nearbyBranchVoxel = refl

crossBranchVoxel :
  hybridVoxel3 Hall.crossBranchNeighbour ≡ LOD.voxel3 2 2 1
crossBranchVoxel = refl

------------------------------------------------------------------------
-- Projection back to the existing branch address is exact.  The local chart
-- digit is forgotten by this projection, so distinct chart states over one
-- branch share the same branch cylinder.

projectBranch2 : LOD.DepthThreeAddress → U369.Address 2
projectBranch2 (a vcons b vcons chart vcons vnil) =
  a vcons b vcons vnil

hybridProjectionReturnsBranch :
  (point : Hall.HybridVisualPoint) →
  projectBranch2 (hybridAddress3 point) ≡ Hall.branchAddress point
hybridProjectionReturnsBranch
  (Hall.hybridVisualPoint (a vcons b vcons vnil) chart) = refl

habitualChartsShareBranchCylinder :
  projectBranch2 (hybridAddress3 Hall.habitualChartOrigin)
  ≡
  projectBranch2 (hybridAddress3 Hall.habitualChartNeighbour)
habitualChartsShareBranchCylinder = refl

habitualChartsRemainDistinctVoxels :
  hybridVoxel3 Hall.habitualChartOrigin ≡ LOD.voxel3 0 0 0
  ×
  hybridVoxel3 Hall.habitualChartNeighbour ≡ LOD.voxel3 0 0 1
habitualChartsRemainDistinctVoxels = refl , refl

------------------------------------------------------------------------
-- Existing hybrid distance and the observation coordinates agree on the
-- decomposition of representative moves: a local deformation changes only the
-- chart digit; a nearby association changes only the second branch digit; a
-- cross-branch plus chart move changes both kinds of coordinates.

localMoveDistanceRegression :
  Hall.hybridDistance
    Hall.habitualChartOrigin
    Hall.habitualChartNeighbour
  ≡
  1
localMoveDistanceRegression = Hall.localChartMoveHasDistanceOne

nearbyBranchDistanceRegression :
  Hall.hybridDistance
    Hall.habitualChartOrigin
    Hall.nearbyBranchOrigin
  ≡
  1
nearbyBranchDistanceRegression = Hall.nearbyBranchMoveHasDistanceOne

crossBranchAndChartDistanceRegression :
  Hall.hybridDistance
    Hall.habitualChartOrigin
    Hall.crossBranchNeighbour
  ≡
  3
crossBranchAndChartDistanceRegression =
  Hall.crossBranchAndChartMoveHasDistanceThree

record HybridPadicReasoningBoundary : Set where
  constructor hybridPadicReasoningBoundary
  field
    chartDigitIsDefinitionallyBranchDigit : Bool
    chartDigitIsDefinitionallyBranchDigitIsFalse :
      chartDigitIsDefinitionallyBranchDigit ≡ false

    branchProjectionRecoversLocalChart : Bool
    branchProjectionRecoversLocalChartIsFalse :
      branchProjectionRecoversLocalChart ≡ false

    combinedAddressRetainsBothCoordinateKinds : Bool
    combinedAddressRetainsBothCoordinateKindsIsTrue :
      combinedAddressRetainsBothCoordinateKinds ≡ true

open HybridPadicReasoningBoundary public

canonicalHybridPadicReasoningBoundary : HybridPadicReasoningBoundary
canonicalHybridPadicReasoningBoundary =
  hybridPadicReasoningBoundary false refl false refl true refl
