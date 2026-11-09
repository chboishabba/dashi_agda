module DASHI.Biology.Physical.Biological369CubicalMaterialFieldExact where

-- IMPORTANT GEOMETRIC CLARIFICATION:
-- The *semantic* physical carrier is the original 3x3x3 cube
-- Cube.Ternary27Point = SSPTrit × SSPTrit × SSPTrit.
-- The Vec Nat 27 is only a bijective STORAGE CHART of that cube.
-- Readout is always labelled by original (x,y,z) cubical positions,
-- retaining all 54 native bonds, 36 plaquettes, and pants seam geometry.

open import DASHI.Core.Prelude

import Data.Vec.Base as V
import Data.Fin.Base as F
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Biology.Physical.BiologicalOriginal54BondSharedVectorExact as Index
import DASHI.Biology.Physical.BiologicalSharedFiniteVectorTransferExact as Transfer
import DASHI.Biology.Physical.BiologicalFullCubeIncidenceExact as Grid

CubicalMaterialField : Set
CubicalMaterialField = Cube.Ternary27Point → Nat

SharedCubicalStorage : Set
SharedCubicalStorage = V.Vec Nat 27

-- A genuine 3D field observation at physical Ternary27Point.
materialAt :
  SharedCubicalStorage → CubicalMaterialField
materialAt inventory point =
  V.lookup inventory (Index.originalPointIndex point)

-- At every original coordinate, indexing and projection agree.
originalCubeReadoutRoundTrip :
  (inventory : SharedCubicalStorage)
  (point : Cube.Ternary27Point) →
  materialAt inventory (Index.originalPointAtIndex
    (Index.originalPointIndex point))
    ≡ materialAt inventory point
originalCubeReadoutRoundTrip inventory point =
  cong (materialAt inventory) (Index.originalPointRoundTrip point)

originalVectorReadoutRoundTrip :
  (inventory : SharedCubicalStorage)
  (i : F.Fin 27) →
  materialAt inventory (Index.originalPointAtIndex i)
    ≡ V.lookup inventory i
originalVectorReadoutRoundTrip inventory i =
  cong (V.lookup inventory) (Index.originalIndexRoundTrip i)

-- One physical positive bond updates the shared storage
-- and the new field can be observed at the SAME original 3D points.
moveAlongOriginalBond :
  Grid.PositiveBond →
  SharedCubicalStorage → SharedCubicalStorage
moveAlongOriginalBond bond inventory =
  Transfer.transferOne
    (Index.originalPointIndex (Grid.bondStart bond))
    (Index.originalPointIndex (Grid.bondEnd bond))
    inventory

cubicalBondTransferConservesTotal :
  (bond : Grid.PositiveBond) (inventory : SharedCubicalStorage) →
  V.sum (moveAlongOriginalBond bond inventory) ≡ V.sum inventory
cubicalBondTransferConservesTotal bond inventory =
  Transfer.everyDirectedPairConservesSharedInventory
    (Index.originalPointIndex (Grid.bondStart bond))
    (Index.originalPointIndex (Grid.bondEnd bond))
    inventory

-- Every material edge is a real geometrical neighbour.
cubicalBondIsNativeNeighbour :
  (bond : Grid.PositiveBond) →
  Cube.HypervoxelAdjacent (Grid.bondStart bond) (Grid.bondEnd bond)
cubicalBondIsNativeNeighbour = Grid.bondIsNearestNeighbour

originalCubicalBondCount : Grid.countList Grid.allPositiveBonds ≡ 54
originalCubicalBondCount = Grid.completeBondCount

originalCubicalPlaquetteCount :
  Grid.countList Grid.allElementarySquares ≡ 36
originalCubicalPlaquetteCount = Grid.completePlaquetteCount

-- Pants gluing is a separate *physical interface witness*, not a
-- reinterpretation of the three Cartesian dimensions as a flat
-- algebraic index, nor proof of any physiological flow coefficient.
