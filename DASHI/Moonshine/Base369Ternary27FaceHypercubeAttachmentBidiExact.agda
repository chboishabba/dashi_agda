module DASHI.Moonshine.Base369Ternary27FaceHypercubeAttachmentBidiExact where

------------------------------------------------------------------------
-- SIX FACE-ATTACHED TERNARY HYPERCUBES
--
-- The Base369 3x3x3 cube owns six literal outer faces.  The finite
-- Heisenberg/Schrodinger model owns six literal ternary coordinates in X6.
-- This file welds those labels by a two-sided chart and then records the
-- face-indexed X6 attachment family.
--
-- Every cube corner is incident to exactly one face from each opposite pair
-- (x-/x+), (y-/y+), (z-/z+), hence to exactly three of the six face labels.
-- This is geometric structure only: no Monster action or gluing theorem is
-- inferred merely from the face count.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Product using (_×_; _,_)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27CornerEightExact as Corners
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H

------------------------------------------------------------------------
-- 1. Literal Face6 <-> Axis6 chart.
------------------------------------------------------------------------

faceToAxis6 : Geometry.Face6 → H.Axis6
faceToAxis6 Geometry.xNegativeFace = H.axis0
faceToAxis6 Geometry.xPositiveFace = H.axis1
faceToAxis6 Geometry.yNegativeFace = H.axis2
faceToAxis6 Geometry.yPositiveFace = H.axis3
faceToAxis6 Geometry.zNegativeFace = H.axis4
faceToAxis6 Geometry.zPositiveFace = H.axis5

axis6ToFace : H.Axis6 → Geometry.Face6
axis6ToFace H.axis0 = Geometry.xNegativeFace
axis6ToFace H.axis1 = Geometry.xPositiveFace
axis6ToFace H.axis2 = Geometry.yNegativeFace
axis6ToFace H.axis3 = Geometry.yPositiveFace
axis6ToFace H.axis4 = Geometry.zNegativeFace
axis6ToFace H.axis5 = Geometry.zPositiveFace

faceAfterAxis : (axis : H.Axis6) → faceToAxis6 (axis6ToFace axis) ≡ axis
faceAfterAxis H.axis0 = refl
faceAfterAxis H.axis1 = refl
faceAfterAxis H.axis2 = refl
faceAfterAxis H.axis3 = refl
faceAfterAxis H.axis4 = refl
faceAfterAxis H.axis5 = refl

axisAfterFace : (face : Geometry.Face6) → axis6ToFace (faceToAxis6 face) ≡ face
axisAfterFace Geometry.xNegativeFace = refl
axisAfterFace Geometry.xPositiveFace = refl
axisAfterFace Geometry.yNegativeFace = refl
axisAfterFace Geometry.yPositiveFace = refl
axisAfterFace Geometry.zNegativeFace = refl
axisAfterFace Geometry.zPositiveFace = refl

------------------------------------------------------------------------
-- 2. Each face indexes one attached X6 hypercube carrier.
------------------------------------------------------------------------

AttachedHypercube : Geometry.Face6 → Set
AttachedHypercube face = H.X6

FaceAttachedHypercube : Set
FaceAttachedHypercube = Geometry.Face6 × H.X6

faceCount : Nat
faceCount = 6

singleHypercubeDimension : Nat
singleHypercubeDimension = H.schrodingerBasisDimension

singleHypercubeDimensionIs729 : singleHypercubeDimension ≡ 729
singleHypercubeDimensionIs729 = refl

sixAttachedHypercubeAddressCount : Nat
sixAttachedHypercubeAddressCount = faceCount * singleHypercubeDimension

sixAttachedHypercubeAddressCountIs4374 :
  sixAttachedHypercubeAddressCount ≡ 4374
sixAttachedHypercubeAddressCountIs4374 = refl

------------------------------------------------------------------------
-- 3. A stronger reading: the six faces can label the six X6 coordinates.
------------------------------------------------------------------------

record FaceCoordinateCube : Set where
  constructor faceCoordinateCube
  field
    xNegativeCoordinate : DASHI.Algebra.Trit.Trit
    xPositiveCoordinate : DASHI.Algebra.Trit.Trit
    yNegativeCoordinate : DASHI.Algebra.Trit.Trit
    yPositiveCoordinate : DASHI.Algebra.Trit.Trit
    zNegativeCoordinate : DASHI.Algebra.Trit.Trit
    zPositiveCoordinate : DASHI.Algebra.Trit.Trit
open FaceCoordinateCube public

x6ToFaceCoordinateCube : H.X6 → FaceCoordinateCube
x6ToFaceCoordinateCube state =
  faceCoordinateCube
    (H.x0 state) (H.x1 state)
    (H.x2 state) (H.x3 state)
    (H.x4 state) (H.x5 state)

faceCoordinateCubeToX6 : FaceCoordinateCube → H.X6
faceCoordinateCubeToX6 state =
  H.x6
    (xNegativeCoordinate state) (xPositiveCoordinate state)
    (yNegativeCoordinate state) (yPositiveCoordinate state)
    (zNegativeCoordinate state) (zPositiveCoordinate state)

faceCoordinateAfterX6 :
  (state : H.X6) →
  faceCoordinateCubeToX6 (x6ToFaceCoordinateCube state) ≡ state
faceCoordinateAfterX6 (H.x6 a b c d e f) = refl

x6AfterFaceCoordinate :
  (state : FaceCoordinateCube) →
  x6ToFaceCoordinateCube (faceCoordinateCubeToX6 state) ≡ state
x6AfterFaceCoordinate (faceCoordinateCube a b c d e f) = refl

------------------------------------------------------------------------
-- 4. Corner incidence: every corner chooses exactly three faces.
------------------------------------------------------------------------

xIncidentFace : Corners.OuterSign → Geometry.Face6
xIncidentFace Corners.negativeOuter = Geometry.xNegativeFace
xIncidentFace Corners.positiveOuter = Geometry.xPositiveFace

yIncidentFace : Corners.OuterSign → Geometry.Face6
yIncidentFace Corners.negativeOuter = Geometry.yNegativeFace
yIncidentFace Corners.positiveOuter = Geometry.yPositiveFace

zIncidentFace : Corners.OuterSign → Geometry.Face6
zIncidentFace Corners.negativeOuter = Geometry.zNegativeFace
zIncidentFace Corners.positiveOuter = Geometry.zPositiveFace

record CornerIncidentFaceTriple : Set where
  constructor cornerIncidentFaceTriple
  field
    incidentXFace : Geometry.Face6
    incidentYFace : Geometry.Face6
    incidentZFace : Geometry.Face6
open CornerIncidentFaceTriple public

cornerIncidentFaces : Corners.Corner3 → CornerIncidentFaceTriple
cornerIncidentFaces (Corners.corner3 x y z) =
  cornerIncidentFaceTriple (xIncidentFace x) (yIncidentFace y) (zIncidentFace z)

cornerOnIncidentXFace :
  (corner : Corners.Corner3) →
  Geometry.OnFace
    (incidentXFace (cornerIncidentFaces corner))
    (Corners.cornerPoint corner)
cornerOnIncidentXFace (Corners.corner3 Corners.negativeOuter y z) = Geometry.onFace refl
cornerOnIncidentXFace (Corners.corner3 Corners.positiveOuter y z) = Geometry.onFace refl

cornerOnIncidentYFace :
  (corner : Corners.Corner3) →
  Geometry.OnFace
    (incidentYFace (cornerIncidentFaces corner))
    (Corners.cornerPoint corner)
cornerOnIncidentYFace (Corners.corner3 x Corners.negativeOuter z) = Geometry.onFace refl
cornerOnIncidentYFace (Corners.corner3 x Corners.positiveOuter z) = Geometry.onFace refl

cornerOnIncidentZFace :
  (corner : Corners.Corner3) →
  Geometry.OnFace
    (incidentZFace (cornerIncidentFaces corner))
    (Corners.cornerPoint corner)
cornerOnIncidentZFace (Corners.corner3 x y Corners.negativeOuter) = Geometry.onFace refl
cornerOnIncidentZFace (Corners.corner3 x y Corners.positiveOuter) = Geometry.onFace refl

------------------------------------------------------------------------
-- 5. Promotion boundary.
------------------------------------------------------------------------

record FaceHypercubeBoundary : Set where
  constructor faceHypercubeBoundary
  field
    sixOuterFacesAlreadyOwned : Bool
    sixHeisenbergAxesAlreadyOwned : Bool
    faceAxisChartTwoSided : Bool
    eachFaceIndexesX6Carrier : Bool
    cornerSelectsThreeIncidentFaces : Bool
    cornerIncidenceProvedOnExistingGeometry : Bool
    faceCoordinateCubeEquivalentToX6 : Bool
    faceAttachmentAloneConstructsMonsterAction : Bool
    cornerIncidenceAloneProvesHypercubeGluing : Bool

canonicalFaceHypercubeBoundary : FaceHypercubeBoundary
canonicalFaceHypercubeBoundary =
  faceHypercubeBoundary true true true true true true true false false
