module DASHI.Biology.IITPointedTernary27CyclotomicCellExact where

------------------------------------------------------------------------
-- POINTED TERNARY-27 <-> C3^3 CYCLOTOMIC CELL CHART
--
-- The geometric 27-cube uses signed coordinates {-1,0,+1}^3.
-- C3CubeFourier27Exact uses C3^3 and an explicit 27-constructor CubeCell27.
-- This file supplies the exact finite carrier chart
--
--   Ternary27Point <-> C3^3 <-> CubeCell27,
--
-- using the signed residue convention -1 -> 2, 0 -> 0, +1 -> 1 mod 3.
-- Thus one selected/active cubie is also one exact Fourier state-cell and one
-- exact character index.  This is a carrier equivalence only: a selected cell
-- is not yet a delta-valued CubeSignal, and cyclic C3 translation is not the
-- same relation as the non-periodic geometric grid adjacency.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Biology.Physical.C3CubeFourier27Exact as Cube
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel
import DASHI.Biology.IITPointedTernary27FaceGluingExact as Pointed

------------------------------------------------------------------------
-- 1. Signed trit <-> C3 phase chart.
------------------------------------------------------------------------

signedTritToPhase : SSP.SSPTrit → Cube.Phase
signedTritToPhase SSP.sspNegOne = Wheel.phase-2
signedTritToPhase SSP.sspZero = Wheel.phase-0
signedTritToPhase SSP.sspPosOne = Wheel.phase-1

phaseToSignedTrit : Cube.Phase → SSP.SSPTrit
phaseToSignedTrit Wheel.phase-0 = SSP.sspZero
phaseToSignedTrit Wheel.phase-1 = SSP.sspPosOne
phaseToSignedTrit Wheel.phase-2 = SSP.sspNegOne

signedTritPhaseRoundTrip :
  (t : SSP.SSPTrit) → phaseToSignedTrit (signedTritToPhase t) ≡ t
signedTritPhaseRoundTrip SSP.sspNegOne = refl
signedTritPhaseRoundTrip SSP.sspZero = refl
signedTritPhaseRoundTrip SSP.sspPosOne = refl

phaseSignedTritRoundTrip :
  (p : Cube.Phase) → signedTritToPhase (phaseToSignedTrit p) ≡ p
phaseSignedTritRoundTrip Wheel.phase-0 = refl
phaseSignedTritRoundTrip Wheel.phase-1 = refl
phaseSignedTritRoundTrip Wheel.phase-2 = refl

------------------------------------------------------------------------
-- 2. Geometric 27-point <-> C3^3.
------------------------------------------------------------------------

pointToC3Cube : Geometry.Ternary27Point → Cube.Cube3
pointToC3Cube (Geometry.ternary27Point x y z) =
  Cube.cube3
    (signedTritToPhase x)
    (signedTritToPhase y)
    (signedTritToPhase z)

c3CubeToPoint : Cube.Cube3 → Geometry.Ternary27Point
c3CubeToPoint (Cube.cube3 x y z) =
  Geometry.ternary27Point
    (phaseToSignedTrit x)
    (phaseToSignedTrit y)
    (phaseToSignedTrit z)

pointC3RoundTrip :
  (point : Geometry.Ternary27Point) →
  c3CubeToPoint (pointToC3Cube point) ≡ point
pointC3RoundTrip (Geometry.ternary27Point x y z)
  rewrite signedTritPhaseRoundTrip x
        | signedTritPhaseRoundTrip y
        | signedTritPhaseRoundTrip z = refl

c3PointRoundTrip :
  (cube : Cube.Cube3) →
  pointToC3Cube (c3CubeToPoint cube) ≡ cube
c3PointRoundTrip (Cube.cube3 x y z)
  rewrite phaseSignedTritRoundTrip x
        | phaseSignedTritRoundTrip y
        | phaseSignedTritRoundTrip z = refl

------------------------------------------------------------------------
-- 3. Geometric 27-point <-> explicit CubeCell27.
------------------------------------------------------------------------

pointToCell27 : Geometry.Ternary27Point → Cube.CubeCell27
pointToCell27 point = Cube.cubeToCell (pointToC3Cube point)

cell27ToPoint : Cube.CubeCell27 → Geometry.Ternary27Point
cell27ToPoint cell = c3CubeToPoint (Cube.cellToCube cell)

pointCell27RoundTrip :
  (point : Geometry.Ternary27Point) →
  cell27ToPoint (pointToCell27 point) ≡ point
pointCell27RoundTrip point
  rewrite Cube.cubeRoundTrip (pointToC3Cube point)
        | pointC3RoundTrip point = refl

cell27PointRoundTrip :
  (cell : Cube.CubeCell27) →
  pointToCell27 (cell27ToPoint cell) ≡ cell
cell27PointRoundTrip cell
  rewrite c3PointRoundTrip (Cube.cellToCube cell)
        | Cube.cellRoundTrip cell = refl

------------------------------------------------------------------------
-- 4. One active cubie becomes one exact 27-cell / character index.
------------------------------------------------------------------------

activeCell27 : Pointed.PointedTernary27Cube → Cube.CubeCell27
activeCell27 pointed = pointToCell27 (Pointed.activeCubie pointed)

activeCharacterIndex :
  Pointed.PointedTernary27Cube → Cube.CharacterIndex
activeCharacterIndex pointed = Cube.cellToCube (activeCell27 pointed)

activeCellCharacterIndexAgreement :
  (pointed : Pointed.PointedTernary27Cube) →
  activeCharacterIndex pointed ≡ Cube.cellToCube (activeCell27 pointed)
activeCellCharacterIndexAgreement pointed = refl

activeCellRecoversSelectedCubie :
  (pointed : Pointed.PointedTernary27Cube) →
  cell27ToPoint (activeCell27 pointed) ≡ Pointed.activeCubie pointed
activeCellRecoversSelectedCubie pointed =
  pointCell27RoundTrip (Pointed.activeCubie pointed)

------------------------------------------------------------------------
-- 5. Geometry/cyclic-action firewall.
------------------------------------------------------------------------

geometricNegativeToPositiveIsNotOneGridStep :
  Geometry.TritGridStep SSP.sspNegOne SSP.sspPosOne → ⊥
geometricNegativeToPositiveIsNotOneGridStep = Geometry.noDirectNegToPos

record PointedCyclotomicCellBoundary : Set where
  constructor pointed-cyclotomic-cell-boundary
  field
    geometric27ChartsExactlyToC3Cubed : Bool
    geometric27ChartsExactlyToCubeCell27 : Bool
    oneActiveCubieSelectsOneCharacterIndex : Bool
    selectedCellIsAlreadyDeltaSignalByDefinition : Bool
    cyclicC3TranslationEqualsNonperiodicGridAdjacency : Bool
    cyclotomicCharacterIndexEqualsIITPhiByDefinition : Bool

open PointedCyclotomicCellBoundary public

canonicalPointedCyclotomicCellBoundary : PointedCyclotomicCellBoundary
canonicalPointedCyclotomicCellBoundary =
  pointed-cyclotomic-cell-boundary
    true true true
    false false false

selectedCellDoesNotManufactureSignalAmplitude :
  selectedCellIsAlreadyDeltaSignalByDefinition
    canonicalPointedCyclotomicCellBoundary ≡ false
selectedCellDoesNotManufactureSignalAmplitude = refl

cyclicAndGeometricAdjacencyRemainDistinct :
  cyclicC3TranslationEqualsNonperiodicGridAdjacency
    canonicalPointedCyclotomicCellBoundary ≡ false
cyclicAndGeometricAdjacencyRemainDistinct = refl

characterIndexDoesNotSelfPromoteToPhi :
  cyclotomicCharacterIndexEqualsIITPhiByDefinition
    canonicalPointedCyclotomicCellBoundary ≡ false
characterIndexDoesNotSelfPromoteToPhi = refl
