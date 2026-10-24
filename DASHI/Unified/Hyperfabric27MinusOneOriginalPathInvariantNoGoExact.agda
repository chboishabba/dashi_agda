module DASHI.Unified.Hyperfabric27MinusOneOriginalPathInvariantNoGoExact where

-- An actual same-geometry obstruction, not a dimension-identity receipt:
-- the original 26 non-origin hypervoxel SITES are not a subgraph closed
-- under the original 27-site path adjacency. This is distinct from the
-- 26-dimensional constant-mode-removed wave space, which IS L-invariant.
-- The Albert F4 traceless-26 is yet another representation requiring an
-- action-preserving intertwiner, not a cardinality bridge.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Wikimedia.IbrahimTernary27OriginTraceless26AlbertShapeBidiExact as Chart

positiveX : Cube.Ternary27Point
positiveX =
  Cube.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero

NonOrigin : Cube.Ternary27Point → Set
NonOrigin p = p ≡ Cube.origin → ⊥

positiveXNonOrigin : NonOrigin positiveX
positiveXNonOrigin ()

-- Import the exact original graph's adjacency, not a second edge relation.
originToPositiveX : Cube.HypervoxelAdjacent Cube.origin positiveX
originToPositiveX = Cube.originAdjacentPositiveX

positiveXToOrigin : Cube.HypervoxelAdjacent positiveX Cube.origin
positiveXToOrigin = Cube.adjacentX Cube.posToZero

-- As soon as a non-origin point is adjacent to the original origin,
-- the proposed 26-point induced physical *closed sector* fails.
NonOriginPathClosed : Set
NonOriginPathClosed =
  (p q : Cube.Ternary27Point) →
  NonOrigin p →
  Cube.HypervoxelAdjacent p q →
  NonOrigin q

nonOriginPathClosedImpossible : NonOriginPathClosed → ⊥
nonOriginPathClosedImpossible closed =
  closed positiveX Cube.origin
    positiveXNonOrigin positiveXToOrigin refl

-- Existing owned site chart still has a valid two-sided round trip.
-- It is this adjacency-invariance condition, not the bijection, that fails.
sameCubeChartRoundTrip :
  (p : Cube.Ternary27Point) →
  Chart.fromAlbertShape (Chart.toAlbertShape p) ≡ p
sameCubeChartRoundTrip = Chart.fromAfterTo
