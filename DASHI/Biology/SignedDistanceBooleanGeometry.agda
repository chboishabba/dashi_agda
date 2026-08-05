module DASHI.Biology.SignedDistanceBooleanGeometry where

open import DASHI.Core.Prelude

import DASHI.Biology.RecursiveSpherePerforation as Perforation

------------------------------------------------------------------------
-- Finite signed-distance / constructive-solid-geometry algebra.
--
-- The sign carrier formalises the exact Boolean semantics needed by a
-- sphere-perforated room.  Magnitudes provide finite safe-step witnesses; no
-- claim is made that this is a complete Euclidean distance estimator.

data DistanceSign : Set where
  insideSign : DistanceSign
  surfaceSign : DistanceSign
  outsideSign : DistanceSign

negateSign : DistanceSign → DistanceSign
negateSign insideSign = outsideSign
negateSign surfaceSign = surfaceSign
negateSign outsideSign = insideSign

maxSign : DistanceSign → DistanceSign → DistanceSign
maxSign insideSign y = y
maxSign surfaceSign insideSign = surfaceSign
maxSign surfaceSign surfaceSign = surfaceSign
maxSign surfaceSign outsideSign = outsideSign
maxSign outsideSign y = outsideSign

minSign : DistanceSign → DistanceSign → DistanceSign
minSign insideSign y = insideSign
minSign surfaceSign insideSign = insideSign
minSign surfaceSign surfaceSign = surfaceSign
minSign surfaceSign outsideSign = surfaceSign
minSign outsideSign y = y

unionSign : DistanceSign → DistanceSign → DistanceSign
unionSign = minSign

intersectionSign : DistanceSign → DistanceSign → DistanceSign
intersectionSign = maxSign

subtractSign : DistanceSign → DistanceSign → DistanceSign
subtractSign solid cutter =
  maxSign solid (negateSign cutter)

data RoomSample : Set where
  retainedWallSample : RoomSample
  sphereInteriorSample : RoomSample
  roomExteriorSample : RoomSample
  sphereBoundarySample : RoomSample

roomSign : RoomSample → DistanceSign
roomSign retainedWallSample = insideSign
roomSign sphereInteriorSample = insideSign
roomSign roomExteriorSample = outsideSign
roomSign sphereBoundarySample = insideSign

sphereSign : RoomSample → DistanceSign
sphereSign retainedWallSample = outsideSign
sphereSign sphereInteriorSample = insideSign
sphereSign roomExteriorSample = outsideSign
sphereSign sphereBoundarySample = surfaceSign

perforatedRoomSign : RoomSample → DistanceSign
perforatedRoomSign p =
  subtractSign (roomSign p) (sphereSign p)

retainedWallRemainsInside :
  perforatedRoomSign retainedWallSample ≡ insideSign
retainedWallRemainsInside = refl

sphereInteriorBecomesOutside :
  perforatedRoomSign sphereInteriorSample ≡ outsideSign
sphereInteriorBecomesOutside = refl

roomExteriorRemainsOutside :
  perforatedRoomSign roomExteriorSample ≡ outsideSign
roomExteriorRemainsOutside = refl

sphereBoundaryBecomesSurface :
  perforatedRoomSign sphereBoundarySample ≡ surfaceSign
sphereBoundaryBecomesSurface = refl

------------------------------------------------------------------------
-- Multiple Boolean subtractions compose recursively.

subtractTwo :
  DistanceSign → DistanceSign → DistanceSign → DistanceSign
subtractTwo solid firstCutter secondCutter =
  subtractSign (subtractSign solid firstCutter) secondCutter

insideEitherCutterIsRemoved :
  subtractTwo insideSign insideSign outsideSign ≡ outsideSign
insideEitherCutterIsRemoved = refl

outsideBothCuttersIsRetained :
  subtractTwo insideSign outsideSign outsideSign ≡ insideSign
outsideBothCuttersIsRetained = refl

------------------------------------------------------------------------
-- Finite domain repetition.

data WorldCoordinate : Set where
  coordinateMinusOne : WorldCoordinate
  coordinateZero : WorldCoordinate
  coordinateOne : WorldCoordinate
  coordinateTwo : WorldCoordinate

data RepeatedCellCoordinate : Set where
  cellMinusOne : RepeatedCellCoordinate
  cellZero : RepeatedCellCoordinate
  cellOne : RepeatedCellCoordinate

repeatToFundamentalCell : WorldCoordinate → RepeatedCellCoordinate
repeatToFundamentalCell coordinateMinusOne = cellMinusOne
repeatToFundamentalCell coordinateZero = cellZero
repeatToFundamentalCell coordinateOne = cellOne
repeatToFundamentalCell coordinateTwo = cellZero

coordinateTwoRepeatsToOriginCell :
  repeatToFundamentalCell coordinateTwo ≡ cellZero
coordinateTwoRepeatsToOriginCell = refl

------------------------------------------------------------------------
-- Finite distance estimates and safe ray steps.

record DistanceSample : Set where
  constructor distanceSample
  field
    sign : DistanceSign
    magnitude : Nat

open DistanceSample public

safeStep : DistanceSample → Nat
safeStep = magnitude

nearSurfaceSample : DistanceSample
nearSurfaceSample = distanceSample outsideSign 1

farSurfaceSample : DistanceSample
farSurfaceSample = distanceSample outsideSign 4

farSampleTakesLargerStep :
  safeStep nearSurfaceSample ≤ safeStep farSurfaceSample
farSampleTakesLargerStep = s≤s z≤n

record SignedDistancePerforationWitness : Set where
  constructor signedDistancePerforationWitness
  field
    removedInterior :
      perforatedRoomSign sphereInteriorSample ≡ outsideSign
    retainedMaterial :
      perforatedRoomSign retainedWallSample ≡ insideSign
    recursivePerforation :
      Perforation.RecursivePerforationBoundary

open SignedDistancePerforationWitness public

canonicalSignedDistancePerforationWitness :
  SignedDistancePerforationWitness
canonicalSignedDistancePerforationWitness =
  signedDistancePerforationWitness
    sphereInteriorBecomesOutside
    retainedWallRemainsInside
    Perforation.canonicalRecursivePerforationBoundary

record SignedDistanceBoundary : Set where
  constructor signedDistanceBoundary
  field
    finiteSignIsExactEuclideanSDF : Bool
    finiteSignIsExactEuclideanSDFIsFalse :
      finiteSignIsExactEuclideanSDF ≡ false

    brainLiterallyRaymarchesThisAlgebra : Bool
    brainLiterallyRaymarchesThisAlgebraIsFalse :
      brainLiterallyRaymarchesThisAlgebra ≡ false

open SignedDistanceBoundary public

canonicalSignedDistanceBoundary : SignedDistanceBoundary
canonicalSignedDistanceBoundary =
  signedDistanceBoundary false refl false refl
