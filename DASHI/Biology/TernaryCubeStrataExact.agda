module DASHI.Biology.TernaryCubeStrataExact where

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic

------------------------------------------------------------------------
-- Binary points occupy only the eight vertices of a three-cube.  Balanced
-- ternary points add edge midpoints, face centres, and the cube centre.

TernaryCubePoint : Set
TernaryCubePoint = Vec Triadic.KernelTrit 3

isZeroTrit : Triadic.KernelTrit → Nat
isZeroTrit Triadic.negativeTrit = 0
isZeroTrit Triadic.zeroTrit = 1
isZeroTrit Triadic.positiveTrit = 0

zeroCoordinateCount : TernaryCubePoint → Nat
zeroCoordinateCount (a vcons b vcons c vcons vnil) =
  isZeroTrit a + isZeroTrit b + isZeroTrit c

data CubeStratum : Set where
  vertexStratum : CubeStratum
  edgeMidpointStratum : CubeStratum
  faceCentreStratum : CubeStratum
  cubeCentreStratum : CubeStratum

stratumOfZeroCount : Nat → CubeStratum
stratumOfZeroCount zero = vertexStratum
stratumOfZeroCount (suc zero) = edgeMidpointStratum
stratumOfZeroCount (suc (suc zero)) = faceCentreStratum
stratumOfZeroCount (suc (suc (suc n))) = cubeCentreStratum

stratumOf : TernaryCubePoint → CubeStratum
stratumOf point = stratumOfZeroCount (zeroCoordinateCount point)

canonicalVertex : TernaryCubePoint
canonicalVertex =
  Triadic.negativeTrit vcons
  Triadic.positiveTrit vcons
  Triadic.negativeTrit vcons
  vnil

canonicalEdgeMidpoint : TernaryCubePoint
canonicalEdgeMidpoint =
  Triadic.zeroTrit vcons
  Triadic.positiveTrit vcons
  Triadic.negativeTrit vcons
  vnil

canonicalFaceCentre : TernaryCubePoint
canonicalFaceCentre =
  Triadic.zeroTrit vcons
  Triadic.zeroTrit vcons
  Triadic.positiveTrit vcons
  vnil

canonicalCubeCentre : TernaryCubePoint
canonicalCubeCentre =
  Triadic.zeroTrit vcons
  Triadic.zeroTrit vcons
  Triadic.zeroTrit vcons
  vnil

canonicalVertexClassifiesExactly :
  stratumOf canonicalVertex ≡ vertexStratum
canonicalVertexClassifiesExactly = refl

canonicalEdgeMidpointClassifiesExactly :
  stratumOf canonicalEdgeMidpoint ≡ edgeMidpointStratum
canonicalEdgeMidpointClassifiesExactly = refl

canonicalFaceCentreClassifiesExactly :
  stratumOf canonicalFaceCentre ≡ faceCentreStratum
canonicalFaceCentreClassifiesExactly = refl

canonicalCubeCentreClassifiesExactly :
  stratumOf canonicalCubeCentre ≡ cubeCentreStratum
canonicalCubeCentreClassifiesExactly = refl

------------------------------------------------------------------------
-- Exact stratum cardinalities in {-1,0,+1}^3.

vertexCount : Nat
vertexCount = 2 * 2 * 2

edgeMidpointCount : Nat
edgeMidpointCount = 3 * 2 * 2

faceCentreCount : Nat
faceCentreCount = 3 * 2

cubeCentreCount : Nat
cubeCentreCount = 1

vertexCountIsEight : vertexCount ≡ 8
vertexCountIsEight = refl

edgeMidpointCountIsTwelve : edgeMidpointCount ≡ 12
edgeMidpointCountIsTwelve = refl

faceCentreCountIsSix : faceCentreCount ≡ 6
faceCentreCountIsSix = refl

cubeCentreCountIsOne : cubeCentreCount ≡ 1
cubeCentreCountIsOne = refl

strataSumToTwentySeven :
  vertexCount + edgeMidpointCount + faceCentreCount + cubeCentreCount ≡ 27
strataSumToTwentySeven = refl

binaryVerticesEmbedAsTernaryVertexStratum :
  vertexCount ≡ 8
binaryVerticesEmbedAsTernaryVertexStratum = refl

record TernaryCubeStrataBoundary : Set where
  constructor ternaryCubeStrataBoundary
  field
    ternaryConvexHullDiffersFromBinaryCubeHull : Bool
    ternaryConvexHullDiffersFromBinaryCubeHullIsFalse :
      ternaryConvexHullDiffersFromBinaryCubeHull ≡ false

    ternaryCombinatoricsContainsOnlyVertices : Bool
    ternaryCombinatoricsContainsOnlyVerticesIsFalse :
      ternaryCombinatoricsContainsOnlyVertices ≡ false

    zeroCoordinateHasOneUniversalSemanticMeaning : Bool
    zeroCoordinateHasOneUniversalSemanticMeaningIsFalse :
      zeroCoordinateHasOneUniversalSemanticMeaning ≡ false

open TernaryCubeStrataBoundary public

canonicalTernaryCubeStrataBoundary : TernaryCubeStrataBoundary
canonicalTernaryCubeStrataBoundary =
  ternaryCubeStrataBoundary false refl false refl false refl
