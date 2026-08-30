module DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact where

------------------------------------------------------------------------
-- BASE369 TERNARY 27-HYPERVOXEL / THREE-CUBE HYPERFABRIC GEOMETRY
--
-- Geometric carrier content:
--   T3 = {-1,0,+1}^3                    27 points
--   H  = T3 x T3 x T3 = {-1,0,+1}^9    19683 points
--
-- The three T3 factors are the existing Base369 interaction cube and the two
-- participant-appraisal cubes. Grid adjacency changes exactly one coordinate
-- by one ternary step: -1 <-> 0 <-> +1.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Empty using (⊥)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369InteractionAppraisalCubeExact as Cube
import DASHI.Foundations.Base369NineCoordinateAggregateBridgeExact as Aggregate

------------------------------------------------------------------------
-- 1. Exact 3 x 3 x 3 ternary hypervoxel.
------------------------------------------------------------------------

data Axis3 : Set where xAxis yAxis zAxis : Axis3

record Ternary27Point : Set where
  constructor ternary27Point
  field
    x : SSP.SSPTrit
    y : SSP.SSPTrit
    z : SSP.SSPTrit
open Ternary27Point public

origin : Ternary27Point
origin = ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero

negativeCorner : Ternary27Point
negativeCorner = ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne

positiveCorner : Ternary27Point
positiveCorner = ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne

axisCount : Nat
axisCount = 3

outerFaceCount : Nat
outerFaceCount = 6

hypervoxelStateCount : Nat
hypervoxelStateCount = 3 * 3 * 3

hypervoxelStateCountIs27 : hypervoxelStateCount ≡ 27
hypervoxelStateCountIs27 = refl

------------------------------------------------------------------------
-- 2. Six outer faces are coordinate hyperplanes at +/-1.
------------------------------------------------------------------------

data Face6 : Set where
  xNegativeFace xPositiveFace yNegativeFace yPositiveFace zNegativeFace zPositiveFace : Face6

faceAxis : Face6 → Axis3
faceAxis xNegativeFace = xAxis
faceAxis xPositiveFace = xAxis
faceAxis yNegativeFace = yAxis
faceAxis yPositiveFace = yAxis
faceAxis zNegativeFace = zAxis
faceAxis zPositiveFace = zAxis

faceLevel : Face6 → SSP.SSPTrit
faceLevel xNegativeFace = SSP.sspNegOne
faceLevel xPositiveFace = SSP.sspPosOne
faceLevel yNegativeFace = SSP.sspNegOne
faceLevel yPositiveFace = SSP.sspPosOne
faceLevel zNegativeFace = SSP.sspNegOne
faceLevel zPositiveFace = SSP.sspPosOne

coordinate : Axis3 → Ternary27Point → SSP.SSPTrit
coordinate xAxis p = x p
coordinate yAxis p = y p
coordinate zAxis p = z p

record OnFace (f : Face6) (p : Ternary27Point) : Set where
  constructor onFace
  field coordinatePinned : coordinate (faceAxis f) p ≡ faceLevel f
open OnFace public

negativeCornerOnXNegative : OnFace xNegativeFace negativeCorner
negativeCornerOnXNegative = onFace refl

positiveCornerOnZPositive : OnFace zPositiveFace positiveCorner
positiveCornerOnZPositive = onFace refl

------------------------------------------------------------------------
-- 3. One-step grid relation.
------------------------------------------------------------------------

data TritGridStep : SSP.SSPTrit → SSP.SSPTrit → Set where
  negToZero : TritGridStep SSP.sspNegOne SSP.sspZero
  zeroToNeg : TritGridStep SSP.sspZero SSP.sspNegOne
  zeroToPos : TritGridStep SSP.sspZero SSP.sspPosOne
  posToZero : TritGridStep SSP.sspPosOne SSP.sspZero

noDirectNegToPos : TritGridStep SSP.sspNegOne SSP.sspPosOne → ⊥
noDirectNegToPos ()

noDirectPosToNeg : TritGridStep SSP.sspPosOne SSP.sspNegOne → ⊥
noDirectPosToNeg ()

data HypervoxelAdjacent : Ternary27Point → Ternary27Point → Set where
  adjacentX : ∀ {x0 x1 y0 z0} → TritGridStep x0 x1 →
    HypervoxelAdjacent (ternary27Point x0 y0 z0) (ternary27Point x1 y0 z0)
  adjacentY : ∀ {x0 y0 y1 z0} → TritGridStep y0 y1 →
    HypervoxelAdjacent (ternary27Point x0 y0 z0) (ternary27Point x0 y1 z0)
  adjacentZ : ∀ {x0 y0 z0 z1} → TritGridStep z0 z1 →
    HypervoxelAdjacent (ternary27Point x0 y0 z0) (ternary27Point x0 y0 z1)

originAdjacentPositiveX :
  HypervoxelAdjacent origin (ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero)
originAdjacentPositiveX = adjacentX zeroToPos

negativeCornerAdjacentXInward :
  HypervoxelAdjacent negativeCorner (ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne)
negativeCornerAdjacentXInward = adjacentX negToZero

------------------------------------------------------------------------
-- 4. Exact three-cube hyperfabric = existing one-round Base369 state.
------------------------------------------------------------------------

record TernaryHyperformalPoint : Set where
  constructor ternaryHyperformalPoint
  field
    interactionVoxel : Ternary27Point
    appraisalAVoxel : Ternary27Point
    appraisalBVoxel : Ternary27Point
open TernaryHyperformalPoint public

fabricCoordinateCount : Nat
fabricCoordinateCount = 9

appraisalFibreStateCount : Nat
appraisalFibreStateCount = 27 * 27

hyperfabricStateCount : Nat
hyperfabricStateCount = 27 * 27 * 27

appraisalFibreStateCountIs729 : appraisalFibreStateCount ≡ 729
appraisalFibreStateCountIs729 = refl

hyperfabricStateCountIs19683 : hyperfabricStateCount ≡ 19683
hyperfabricStateCountIs19683 = refl

pointToInteractionCube : Ternary27Point → Cube.InteractionCube
pointToInteractionCube (ternary27Point a b c) = Cube.interactionCube a b c

interactionCubeToPoint : Cube.InteractionCube → Ternary27Point
interactionCubeToPoint (Cube.interactionCube a b c) = ternary27Point a b c

pointToParticipantAppraisal : Ternary27Point → Cube.ParticipantAppraisal
pointToParticipantAppraisal (ternary27Point a b c) = Cube.participantAppraisal a b c

participantAppraisalToPoint : Cube.ParticipantAppraisal → Ternary27Point
participantAppraisalToPoint (Cube.participantAppraisal a b c) = ternary27Point a b c

pointInteractionRoundTrip : (p : Ternary27Point) → interactionCubeToPoint (pointToInteractionCube p) ≡ p
pointInteractionRoundTrip (ternary27Point a b c) = refl

interactionPointRoundTrip : (c : Cube.InteractionCube) → pointToInteractionCube (interactionCubeToPoint c) ≡ c
interactionPointRoundTrip (Cube.interactionCube a b c) = refl

pointAppraisalRoundTrip : (p : Ternary27Point) → participantAppraisalToPoint (pointToParticipantAppraisal p) ≡ p
pointAppraisalRoundTrip (ternary27Point a b c) = refl

appraisalPointRoundTrip : (a : Cube.ParticipantAppraisal) → pointToParticipantAppraisal (participantAppraisalToPoint a) ≡ a
appraisalPointRoundTrip (Cube.participantAppraisal a b c) = refl

fabricToRound : TernaryHyperformalPoint → Cube.OneRoundInteractionState
fabricToRound (ternaryHyperformalPoint interaction appA appB) =
  Cube.oneRoundInteractionState
    (pointToInteractionCube interaction)
    (Cube.appraisalFibre (pointToParticipantAppraisal appA) (pointToParticipantAppraisal appB))

roundToFabric : Cube.OneRoundInteractionState → TernaryHyperformalPoint
roundToFabric (Cube.oneRoundInteractionState interaction (Cube.appraisalFibre appA appB)) =
  ternaryHyperformalPoint
    (interactionCubeToPoint interaction)
    (participantAppraisalToPoint appA)
    (participantAppraisalToPoint appB)

fabricRoundTrip : (p : TernaryHyperformalPoint) → roundToFabric (fabricToRound p) ≡ p
fabricRoundTrip
  (ternaryHyperformalPoint (ternary27Point a b c) (ternary27Point d e f) (ternary27Point g h i)) = refl

roundFabricRoundTrip : (s : Cube.OneRoundInteractionState) → fabricToRound (roundToFabric s) ≡ s
roundFabricRoundTrip
  (Cube.oneRoundInteractionState (Cube.interactionCube a b c)
    (Cube.appraisalFibre (Cube.participantAppraisal d e f) (Cube.participantAppraisal g h i))) = refl

------------------------------------------------------------------------
-- 5. Flat SSPTrit^9 chart is exactly the same fabric.
------------------------------------------------------------------------

fabricToNineTrits : TernaryHyperformalPoint → Aggregate.NineTrits
fabricToNineTrits
  (ternaryHyperformalPoint (ternary27Point a b c) (ternary27Point d e f) (ternary27Point g h i)) =
  Aggregate.nineTrits a b c d e f g h i

nineTritsToFabric : Aggregate.NineTrits → TernaryHyperformalPoint
nineTritsToFabric (Aggregate.nineTrits a b c d e f g h i) =
  ternaryHyperformalPoint (ternary27Point a b c) (ternary27Point d e f) (ternary27Point g h i)

fabricNineRoundTrip : (p : TernaryHyperformalPoint) → nineTritsToFabric (fabricToNineTrits p) ≡ p
fabricNineRoundTrip
  (ternaryHyperformalPoint (ternary27Point a b c) (ternary27Point d e f) (ternary27Point g h i)) = refl

nineFabricRoundTrip : (n : Aggregate.NineTrits) → fabricToNineTrits (nineTritsToFabric n) ≡ n
nineFabricRoundTrip (Aggregate.nineTrits a b c d e f g h i) = refl

flattenRoundAgreesWithFabricChart : (p : TernaryHyperformalPoint) →
  Aggregate.flattenRound (fabricToRound p) ≡ fabricToNineTrits p
flattenRoundAgreesWithFabricChart
  (ternaryHyperformalPoint (ternary27Point a b c) (ternary27Point d e f) (ternary27Point g h i)) = refl

------------------------------------------------------------------------
-- 6. Literal fibre geometry: 729 appraisal points above each interaction voxel.
------------------------------------------------------------------------

projectInteractionVoxel : TernaryHyperformalPoint → Ternary27Point
projectInteractionVoxel = interactionVoxel

record AppraisalFibrePoint : Set where
  constructor appraisalFibrePoint
  field
    appraisalAPoint : Ternary27Point
    appraisalBPoint : Ternary27Point
open AppraisalFibrePoint public

projectAppraisalFibre : TernaryHyperformalPoint → AppraisalFibrePoint
projectAppraisalFibre p = appraisalFibrePoint (appraisalAVoxel p) (appraisalBVoxel p)

rebuildOverInteraction : Ternary27Point → AppraisalFibrePoint → TernaryHyperformalPoint
rebuildOverInteraction i (appraisalFibrePoint a b) = ternaryHyperformalPoint i a b

projectionRebuildInteraction : (i : Ternary27Point) → (f : AppraisalFibrePoint) →
  projectInteractionVoxel (rebuildOverInteraction i f) ≡ i
projectionRebuildInteraction i f = refl

projectionRebuildFibre : (i : Ternary27Point) → (f : AppraisalFibrePoint) →
  projectAppraisalFibre (rebuildOverInteraction i f) ≡ f
projectionRebuildFibre i (appraisalFibrePoint a b) = refl

------------------------------------------------------------------------
-- 7. Hyperformal adjacency changes one coordinate in one 27-cube only.
------------------------------------------------------------------------

data HyperformalAdjacent : TernaryHyperformalPoint → TernaryHyperformalPoint → Set where
  interactionAdjacent : ∀ {i0 i1 a b} → HypervoxelAdjacent i0 i1 →
    HyperformalAdjacent (ternaryHyperformalPoint i0 a b) (ternaryHyperformalPoint i1 a b)
  appraisalAAdjacent : ∀ {i a0 a1 b} → HypervoxelAdjacent a0 a1 →
    HyperformalAdjacent (ternaryHyperformalPoint i a0 b) (ternaryHyperformalPoint i a1 b)
  appraisalBAdjacent : ∀ {i a b0 b1} → HypervoxelAdjacent b0 b1 →
    HyperformalAdjacent (ternaryHyperformalPoint i a b0) (ternaryHyperformalPoint i a b1)

fabricOrigin : TernaryHyperformalPoint
fabricOrigin = ternaryHyperformalPoint origin origin origin

fabricOriginInteractionXNeighbour : TernaryHyperformalPoint
fabricOriginInteractionXNeighbour =
  ternaryHyperformalPoint (ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero) origin origin

fabricOriginAdjacentAlongInteractionX :
  HyperformalAdjacent fabricOrigin fabricOriginInteractionXNeighbour
fabricOriginAdjacentAlongInteractionX = interactionAdjacent originAdjacentPositiveX

------------------------------------------------------------------------
-- 8. Geometric boundary: numerical coincidences do not create semantics.
------------------------------------------------------------------------

record Ternary27HypervoxelGeometryBoundary : Set where
  constructor ternary27HypervoxelGeometryBoundary
  field
    oneCubeIsThreeTernaryCoordinates : Bool
    oneCubeHasTwentySevenStates : Bool
    oneCubeHasSixOuterFaces : Bool
    threeCubesHaveNineCoordinates : Bool
    appraisalFibreHasSevenHundredTwentyNineStates : Bool
    threeCubeFabricHasNineteenThousandSixHundredEightyThreeStates : Bool
    directNegativeToPositiveIsGridEdge : Bool
    shared369NumeralsImplySharedSemanticRole : Bool

canonicalTernary27HypervoxelGeometryBoundary : Ternary27HypervoxelGeometryBoundary
canonicalTernary27HypervoxelGeometryBoundary =
  ternary27HypervoxelGeometryBoundary true true true true true true false false
