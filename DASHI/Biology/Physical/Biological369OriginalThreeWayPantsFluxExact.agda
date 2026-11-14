module DASHI.Biology.Physical.Biological369OriginalThreeWayPantsFluxExact where

------------------------------------------------------------------------
-- GENUINE 1-to-3 THREE-CUBE PHYSICAL PANTS BRANCHING.
--
-- Original geometric carrier: SSPTrit^3, 27 voxels and 54
-- native nearest-neighbour bonds. At (0,0,0) three independent
-- source-certified outgoing bonds reach (+1,0,0), (0,+1,0),
-- (0,0,+1). All three share ONE original physical inventory.
--
-- Canonical pants from RelationalBranchCobordismGeometry has
-- one incoming capacity 3, three fine outputs of capacity 1,
-- and exact composition/conservation. This specific selected
-- integer material fixture realizes 3 -> 1+1+1; it does NOT
-- prove that generic pants branch capacity is molar flux or
-- that a biological branching vessel has such rates.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Data.Vec.Base as V
import Data.Fin.Base as F
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Biology.Physical.BiologicalFullCubeIncidenceExact as Grid
import DASHI.Biology.Physical.BiologicalOriginal54BondSharedVectorExact as Index
import DASHI.Biology.Physical.BiologicalSharedFiniteVectorTransferExact as Transfer
import DASHI.Biology.Physical.Biological369CubicalBoundaryMaterialExact as Inject
import DASHI.Reasoning.RelationalBranchCobordismGeometry as Pants
import DASHI.Topology.TernaryCylinderPantsGeometryExact as CylinderPants

originalXPositiveBranch : Grid.PositiveBond
originalXPositiveBranch = Grid.xBond Grid.upper SSP.sspZero SSP.sspZero

originalYPositiveBranch : Grid.PositiveBond
originalYPositiveBranch = Grid.yBond SSP.sspZero Grid.upper SSP.sspZero

originalZPositiveBranch : Grid.PositiveBond
originalZPositiveBranch = Grid.zBond SSP.sspZero SSP.sspZero Grid.upper

originalThreeBranchesSharePhysicalOrigin :
  Grid.bondStart originalXPositiveBranch ≡ Cube.origin
    × (Grid.bondStart originalYPositiveBranch ≡ Cube.origin
    × Grid.bondStart originalZPositiveBranch ≡ Cube.origin)
originalThreeBranchesSharePhysicalOrigin = refl , (refl , refl)

originalXIsPhysicalNeighbour :
  Cube.HypervoxelAdjacent Cube.origin
    (Grid.bondEnd originalXPositiveBranch)
originalXIsPhysicalNeighbour =
  Grid.bondIsNearestNeighbour originalXPositiveBranch

originalYIsPhysicalNeighbour :
  Cube.HypervoxelAdjacent Cube.origin
    (Grid.bondEnd originalYPositiveBranch)
originalYIsPhysicalNeighbour =
  Grid.bondIsNearestNeighbour originalYPositiveBranch

originalZIsPhysicalNeighbour :
  Cube.HypervoxelAdjacent Cube.origin
    (Grid.bondEnd originalZPositiveBranch)
originalZIsPhysicalNeighbour =
  Grid.bondIsNearestNeighbour originalZPositiveBranch

physicalBranchAction :
  Grid.PositiveBond → (F.Fin 27 × F.Fin 27)
physicalBranchAction bond =
  Index.originalPointIndex (Grid.bondStart bond) ,
  Index.originalPointIndex (Grid.bondEnd bond)

originalThreeWayPantsActions : List (F.Fin 27 × F.Fin 27)
originalThreeWayPantsActions =
  physicalBranchAction originalXPositiveBranch
  ∷ physicalBranchAction originalYPositiveBranch
  ∷ physicalBranchAction originalZPositiveBranch
  ∷ []

originalThreeWayPantsActionCount :
  Grid.countList originalThreeWayPantsActions ≡ 3
originalThreeWayPantsActionCount = refl

selectedThreeAtOriginalPhysicalOrigin : V.Vec Nat 27
selectedThreeAtOriginalPhysicalOrigin =
  Inject.injectAtIndex
    (Index.originalPointIndex Cube.origin)
    3
    (V.replicate 27 0)

originalThreeWayPantsResult : V.Vec Nat 27
originalThreeWayPantsResult =
  Transfer.runTransfers originalThreeWayPantsActions
    selectedThreeAtOriginalPhysicalOrigin

-- This exact original physical branching instance has no new source;
-- it transports the same three initial material quanta.
originalThreeWayPantsConservesSameInventory :
  V.sum originalThreeWayPantsResult
    ≡ V.sum selectedThreeAtOriginalPhysicalOrigin
originalThreeWayPantsConservesSameInventory =
  Transfer.all27SharedSitesConserve
    originalThreeWayPantsActions
    selectedThreeAtOriginalPhysicalOrigin

selectedMaterialAmountExactlyThree :
  V.sum selectedThreeAtOriginalPhysicalOrigin ≡ 3
selectedMaterialAmountExactlyThree = refl

selectedBranchedMaterialAmountExactlyThree :
  V.sum originalThreeWayPantsResult ≡ 3
selectedBranchedMaterialAmountExactlyThree =
  trans
    originalThreeWayPantsConservesSameInventory
    selectedMaterialAmountExactlyThree

xOutputReceivesOne :
  V.lookup originalThreeWayPantsResult
    (Index.originalPointIndex (Grid.bondEnd originalXPositiveBranch))
    ≡ 1
xOutputReceivesOne = refl

yOutputReceivesOne :
  V.lookup originalThreeWayPantsResult
    (Index.originalPointIndex (Grid.bondEnd originalYPositiveBranch))
    ≡ 1
yOutputReceivesOne = refl

zOutputReceivesOne :
  V.lookup originalThreeWayPantsResult
    (Index.originalPointIndex (Grid.bondEnd originalZPositiveBranch))
    ≡ 1
zOutputReceivesOne = refl

sourceOriginDepletedAfterThreeTransfers :
  V.lookup originalThreeWayPantsResult
    (Index.originalPointIndex Cube.origin)
    ≡ 0
sourceOriginDepletedAfterThreeTransfers = refl

-- Reuse the EXACT original compiled 1-to-3 pants capacity and
-- output-channel theorem rather than manufacturing a replacement.
canonicalOneToThreePantsCapacity :
  Pants.CapacityConservative Pants.composedOneToThree
canonicalOneToThreePantsCapacity =
  CylinderPants.canonicalPantsCapacityConservative

originalPantsHasThreeChannels :
  Pants.outputCount Pants.composedOneToThree ≡ 3
originalPantsHasThreeChannels =
  CylinderPants.canonicalPantsHasThreeOutputs

originalPantsInputCapacityEqualsPhysicalFixture :
  Pants.inputCapacity Pants.composedOneToThree
    ≡ V.sum selectedThreeAtOriginalPhysicalOrigin
originalPantsInputCapacityEqualsPhysicalFixture = refl

originalPantsOutputCapacityEqualsPhysicalFixture :
  Pants.outputCapacity Pants.composedOneToThree
    ≡ V.sum originalThreeWayPantsResult
originalPantsOutputCapacityEqualsPhysicalFixture = refl

-- This branch capacity / molecule-count identification is justified
-- ONLY by the above concrete selected 3/1/1/1 fixture. It is not a
-- universal map from logical branch-channel amplitude to biology.
data ArbitraryPantsAutomaticallyMeasuresBiologicalFlux : Set where

pantsCapacityDoesNotPayEmpiricalFlux :
  ArbitraryPantsAutomaticallyMeasuresBiologicalFlux → ⊥
pantsCapacityDoesNotPayEmpiricalFlux ()
