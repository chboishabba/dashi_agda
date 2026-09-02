module DASHI.Base369Monster3BFaceHypercubeValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27CornerEightExact as Corners
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Base369Ternary27FaceHypercubeAttachmentBidiExact as Face
import DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound13Exact as Round13

positiveCorner : Corners.Corner3
positiveCorner =
  Corners.corner3 Corners.positiveOuter Corners.positiveOuter Corners.positiveOuter

faceAxisRoundTrip :
  (face : Geometry.Face6) →
  Face.axis6ToFace (Face.faceToAxis6 face) ≡ face
faceAxisRoundTrip = Face.axisAfterFace

axisFaceRoundTrip :
  (axis : H.Axis6) →
  Face.faceToAxis6 (Face.axis6ToFace axis) ≡ axis
axisFaceRoundTrip = Face.faceAfterAxis

positiveCornerOnItsXFace :
  Geometry.OnFace Geometry.xPositiveFace (Corners.cornerPoint positiveCorner)
positiveCornerOnItsXFace = Face.cornerOnIncidentXFace positiveCorner

positiveCornerOnItsYFace :
  Geometry.OnFace Geometry.yPositiveFace (Corners.cornerPoint positiveCorner)
positiveCornerOnItsYFace = Face.cornerOnIncidentYFace positiveCorner

positiveCornerOnItsZFace :
  Geometry.OnFace Geometry.zPositiveFace (Corners.cornerPoint positiveCorner)
positiveCornerOnItsZFace = Face.cornerOnIncidentZFace positiveCorner

sixFaceHypercubeCount : Face.sixAttachedHypercubeAddressCount ≡ 4374
sixFaceHypercubeCount = Face.sixAttachedHypercubeAddressCountIs4374

faceGeometryOwned :
  Round13.Round13Status.face6ToAxis6TwoSided Round13.canonicalRound13Status ≡ true
faceGeometryOwned = refl

actualGluingStillLive :
  Round13.Round13Status.faceAttachedHypercubesHaveActualMonsterGluing
    Round13.canonicalRound13Status ≡ false
actualGluingStillLive = refl
