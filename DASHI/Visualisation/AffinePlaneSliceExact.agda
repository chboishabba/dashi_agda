module DASHI.Visualisation.AffinePlaneSliceExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Finite coordinate carrier for affine two-plane slicing in four ambient
-- coordinates.  Nat coordinates keep the arithmetic executable; the module
-- records, rather than assumes, the remaining real/Stiefel obligations.

record Point4 : Set where
  constructor point4
  field
    coordinateOne : Nat
    coordinateTwo : Nat
    coordinateThree : Nat
    coordinateFour : Nat

open Point4 public

addPoint : Point4 → Point4 → Point4
addPoint (point4 a b c d) (point4 e f g h) =
  point4 (a + e) (b + f) (c + g) (d + h)

scalePoint : Nat → Point4 → Point4
scalePoint n (point4 a b c d) =
  point4 (n * a) (n * b) (n * c) (n * d)

record AffinePlane : Set where
  constructor affinePlane
  field
    origin : Point4
    directionA : Point4
    directionB : Point4

open AffinePlane public

slicePoint : AffinePlane → Nat → Nat → Point4
slicePoint plane u v =
  addPoint
    (addPoint
      (origin plane)
      (scalePoint u (directionA plane)))
    (scalePoint v (directionB plane))

axisAlignedPlane : AffinePlane
axisAlignedPlane =
  affinePlane
    (point4 0 0 2 3)
    (point4 1 0 0 0)
    (point4 0 1 0 0)

angledPlane : AffinePlane
angledPlane =
  affinePlane
    (point4 0 0 1 1)
    (point4 1 0 1 1)
    (point4 0 1 0 1)

axisAlignedSample :
  slicePoint axisAlignedPlane 2 3 ≡ point4 2 3 2 3
axisAlignedSample = refl

angledSample :
  slicePoint angledPlane 2 3 ≡ point4 2 3 3 6
angledSample = refl

------------------------------------------------------------------------
-- The same affine plane admits shifted origins and changed in-plane bases.
-- This finite witness moves the origin by direction A and compensates by one
-- unit of the first slice coordinate.

shiftOriginByA : AffinePlane → AffinePlane
shiftOriginByA plane =
  affinePlane
    (addPoint (origin plane) (directionA plane))
    (directionA plane)
    (directionB plane)

originShiftSameSample :
  slicePoint axisAlignedPlane 1 0
  ≡
  slicePoint (shiftOriginByA axisAlignedPlane) 0 0
originShiftSameSample = refl

swapBasis : AffinePlane → AffinePlane
swapBasis plane =
  affinePlane
    (origin plane)
    (directionB plane)
    (directionA plane)

basisSwapReparameterises :
  slicePoint (swapBasis angledPlane) 2 3
  ≡
  slicePoint angledPlane 3 2
basisSwapReparameterises = refl

------------------------------------------------------------------------
-- Search-family metadata.  A graph-of-slopes chart is useful but does not
-- represent every plane orientation.

data PlaneSearchFamily : Set where
  slopeChartFamily : PlaneSearchFamily
  orthonormalFrameFamily : PlaneSearchFamily

orientationDegreesInGrTwoFour : Nat
orientationDegreesInGrTwoFour = 4

normalOffsetDegreesInFourSpace : Nat
normalOffsetDegreesInFourSpace = 2

affinePlaneDegrees : Nat
affinePlaneDegrees =
  orientationDegreesInGrTwoFour + normalOffsetDegreesInFourSpace

affinePlaneDegreesAreSix : affinePlaneDegrees ≡ 6
affinePlaneDegreesAreSix = refl

record AffinePlaneSliceBoundary : Set where
  constructor affinePlaneSliceBoundary
  field
    slopeChartCoversEveryTwoPlaneInFourSpace : Bool
    slopeChartCoversEveryTwoPlaneInFourSpaceIsFalse :
      slopeChartCoversEveryTwoPlaneInFourSpace ≡ false

    bestSampledPlaneIsGlobalGrassmannianOptimum : Bool
    bestSampledPlaneIsGlobalGrassmannianOptimumIsFalse :
      bestSampledPlaneIsGlobalGrassmannianOptimum ≡ false

    finiteNatFrameIsContinuumStiefelProof : Bool
    finiteNatFrameIsContinuumStiefelProofIsFalse :
      finiteNatFrameIsContinuumStiefelProof ≡ false

open AffinePlaneSliceBoundary public

canonicalAffinePlaneSliceBoundary : AffinePlaneSliceBoundary
canonicalAffinePlaneSliceBoundary =
  affinePlaneSliceBoundary false refl false refl false refl
