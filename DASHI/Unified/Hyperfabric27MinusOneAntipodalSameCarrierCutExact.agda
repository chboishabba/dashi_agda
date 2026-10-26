module DASHI.Unified.Hyperfabric27MinusOneAntipodalSameCarrierCutExact where

-- Reuses the exact original 27-site spatial cube and the already proved
-- origin + 26 (Albert-shaped) two-sided chart. The NEW theorem in this
-- tranche is the native cube antipodal involution, its graph compatibility,
-- and uniqueness of its fixed point, not a second 26-element enumeration.
-- 13 opposite pairs are a finite mathematical reflection of 26 nonorigin
-- points; parity of waves must not be promoted to physical chirality.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_+_; _*_)

open import Data.Empty using (⊥)
open import Data.Sum.Base using (inj₁)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Wikimedia.IbrahimTernary27OriginTraceless26AlbertShapeBidiExact as Chart
import DASHI.Wikimedia.IbrahimA027907PathCubeTernaryExceptionalThirteenSnowballExact as Thirteen
import DASHI.Foundations.ExceptionalAlbertFreudenthalResidualExact as Albert

negateTrit : SSP.SSPTrit → SSP.SSPTrit
negateTrit SSP.sspNegOne = SSP.sspPosOne
negateTrit SSP.sspZero = SSP.sspZero
negateTrit SSP.sspPosOne = SSP.sspNegOne

negateTritInvolutive : (x : SSP.SSPTrit) →
  negateTrit (negateTrit x) ≡ x
negateTritInvolutive SSP.sspNegOne = refl
negateTritInvolutive SSP.sspZero = refl
negateTritInvolutive SSP.sspPosOne = refl

antipode : Cube.Ternary27Point → Cube.Ternary27Point
antipode (Cube.ternary27Point x y z) =
  Cube.ternary27Point (negateTrit x) (negateTrit y) (negateTrit z)

antipodeInvolutive : (p : Cube.Ternary27Point) →
  antipode (antipode p) ≡ p
antipodeInvolutive (Cube.ternary27Point x y z)
  rewrite negateTritInvolutive x
        | negateTritInvolutive y
        | negateTritInvolutive z = refl

originIsAntipodeFixed : antipode Cube.origin ≡ Cube.origin
originIsAntipodeFixed = refl

onlyAntipodeFixedPointIsOrigin : (p : Cube.Ternary27Point) →
  antipode p ≡ p → p ≡ Cube.origin
onlyAntipodeFixedPointIsOrigin
  (Cube.ternary27Point SSP.sspNegOne y z) ()
onlyAntipodeFixedPointIsOrigin
  (Cube.ternary27Point SSP.sspPosOne y z) ()
onlyAntipodeFixedPointIsOrigin
  (Cube.ternary27Point SSP.sspZero SSP.sspNegOne z) ()
onlyAntipodeFixedPointIsOrigin
  (Cube.ternary27Point SSP.sspZero SSP.sspPosOne z) ()
onlyAntipodeFixedPointIsOrigin
  (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne) ()
onlyAntipodeFixedPointIsOrigin
  (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne) ()
onlyAntipodeFixedPointIsOrigin
  (Cube.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero) refl = refl

invertPathStep : ∀ {a b} →
  Cube.TritGridStep a b →
  Cube.TritGridStep (negateTrit a) (negateTrit b)
invertPathStep Cube.negToZero = Cube.posToZero
invertPathStep Cube.zeroToNeg = Cube.zeroToPos
invertPathStep Cube.zeroToPos = Cube.zeroToNeg
invertPathStep Cube.posToZero = Cube.negToZero

antipodePreservesOriginalPathAdjacency :
  ∀ {p q} → Cube.HypervoxelAdjacent p q →
  Cube.HypervoxelAdjacent (antipode p) (antipode q)
antipodePreservesOriginalPathAdjacency (Cube.adjacentX step) =
  Cube.adjacentX (invertPathStep step)
antipodePreservesOriginalPathAdjacency (Cube.adjacentY step) =
  Cube.adjacentY (invertPathStep step)
antipodePreservesOriginalPathAdjacency (Cube.adjacentZ step) =
  Cube.adjacentZ (invertPathStep step)

-- Existing direct two-sided ORIGINAL 27-point chart (not a new chart).
sameSpatialCubeAlbertChartRoundTrip : (p : Cube.Ternary27Point) →
  Chart.fromAlbertShape (Chart.toAlbertShape p) ≡ p
sameSpatialCubeAlbertChartRoundTrip = Chart.fromAfterTo

sameAlbertChartSpatialRoundTrip : (a : Chart.CubeAlbert27) →
  Chart.toAlbertShape (Chart.fromAlbertShape a) ≡ a
sameAlbertChartSpatialRoundTrip = Chart.toAfterFrom

originIsChosenScalarChart :
  Chart.toAlbertShape Cube.origin ≡
  inj₁ Albert.scalarLine
originIsChosenScalarChart = Chart.originMapsToScalar

-- External Albert dimensions and preexisting 13+13 row arithmetic only.
existingAlbert27SplitsOneAnd26 : 27 ≡ 1 + 26
existingAlbert27SplitsOneAnd26 = Albert.albertSplitsScalarPlusTraceless

existingTwentySixAsThirteenPair : 26 ≡ 2 * 13
existingTwentySixAsThirteenPair = Thirteen.twentySixAsTwoThirteen

-- Not implied: this chosen site chart preserves the exceptional Jordan
-- product, an F4/E6 action, a physical 26D bosonic string target, a c=26
-- conformal VOA or BRST cohomology. Those require separate same-object data.
