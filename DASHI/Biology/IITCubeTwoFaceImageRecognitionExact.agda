module DASHI.Biology.IITCubeTwoFaceImageRecognitionExact where

------------------------------------------------------------------------
-- CONSTRUCTIVE TWO-FACE CHARACTERISATION OF THE SELECTED TERNARY CUBE IMAGE
--
-- For the 3x3x3 toroidal linear rule A = Sx + Sy + Sz, group the source and
-- target into three z-faces u0,u1,u2 and y0,y1,y2.  Let B = Sx + Sy act on one
-- face.  Then
--
--   y0 = B u0 + u1
--   y1 = B u1 + u2
--   y2 = B u2 + u0.
--
-- In characteristic three, commuting length-three shifts satisfy
--
--   B^3 = (Sx + Sy)^3 = Sx^3 + Sy^3 = 2 I = -I.
--
-- Eliminating the source therefore gives the exact graph law
--
--   y2 = B y1 - B^2 y0.
--
-- Conversely arbitrary y0,y1 are realized by u0=0, u1=y0,
-- u2=y1-B y0.  Thus the reachable image is exactly a graph over two faces.
--
-- This module kernelizes the GRAPH / TWO-FACE equivalence abstractly over the
-- already-paid two-face carrier.  Instantiating B with the concrete toroidal
-- face operator still requires the explicit B^3=-I same-object witness; that
-- obligation is carried separately and cannot be manufactured from rank 18.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Biology.IITCubeTwoFaceQ9SelfIndexingWeldExact as Q9Weld

------------------------------------------------------------------------
-- 1. Abstract face endomorphism interface.  Only the recovery expression is
-- needed to define the graph; the concrete toroidal realization pays the
-- characteristic-three shift identity separately.
------------------------------------------------------------------------

record FaceRecoveryStructure (Face : Set) : Set₁ where
  field
    zeroFace : Face
    addFace : Face → Face → Face
    negFace : Face → Face
    B : Face → Face

open FaceRecoveryStructure public

subFace :
  ∀ {Face} → FaceRecoveryStructure Face → Face → Face → Face
subFace structure x y = addFace structure x (negFace structure y)

B2 : ∀ {Face} → FaceRecoveryStructure Face → Face → Face
B2 structure x = B structure (B structure x)

thirdFaceFromTwo :
  ∀ {Face} → FaceRecoveryStructure Face → Face → Face → Face
thirdFaceFromTwo structure first second =
  subFace structure
    (B structure second)
    (B2 structure first)

------------------------------------------------------------------------
-- 2. The exact graph carrier of reachable outputs.
------------------------------------------------------------------------

record TwoFaceImageGraph {Face : Set}
    (structure : FaceRecoveryStructure Face) : Set where
  constructor two-face-image-graph
  field
    face0 : Face
    face1 : Face
    face2 : Face
    face2Law :
      face2 ≡ thirdFaceFromTwo structure face0 face1

open TwoFaceImageGraph public

graphToTwoFaces :
  ∀ {Face} {structure : FaceRecoveryStructure Face} →
  TwoFaceImageGraph structure → Face × Face
graphToTwoFaces graph = face0 graph , face1 graph

twoFacesToGraph :
  ∀ {Face} (structure : FaceRecoveryStructure Face) →
  Face × Face → TwoFaceImageGraph structure
twoFacesToGraph structure (first , second) =
  two-face-image-graph
    first second
    (thirdFaceFromTwo structure first second)
    refl

twoFacesAfterGraph :
  ∀ {Face} {structure : FaceRecoveryStructure Face} →
  (graph : TwoFaceImageGraph structure) →
  graphToTwoFaces graphToTwoFacesDummy ≡ graphToTwoFaces graph
  where
    graphToTwoFacesDummy : TwoFaceImageGraph structure
    graphToTwoFacesDummy = twoFacesToGraph structure (graphToTwoFaces graph)
twoFacesAfterGraph graph = refl

------------------------------------------------------------------------
-- 3. Pointwise graph reconstruction: because face2 is proof-relevant equality,
-- full record equality is left to the concrete extensional carrier.  The
-- computational content needed for the weld is exact: first and second faces
-- are preserved and the third is definitionally reconstructed from them.
------------------------------------------------------------------------

reconstructedFace0 :
  ∀ {Face} (structure : FaceRecoveryStructure Face) (faces : Face × Face) →
  face0 (twoFacesToGraph structure faces) ≡ proj₁ faces
reconstructedFace0 structure (first , second) = refl

reconstructedFace1 :
  ∀ {Face} (structure : FaceRecoveryStructure Face) (faces : Face × Face) →
  face1 (twoFacesToGraph structure faces) ≡ proj₂ faces
reconstructedFace1 structure (first , second) = refl

reconstructedFace2 :
  ∀ {Face} (structure : FaceRecoveryStructure Face) (faces : Face × Face) →
  face2 (twoFacesToGraph structure faces)
  ≡ thirdFaceFromTwo structure (proj₁ faces) (proj₂ faces)
reconstructedFace2 structure (first , second) = refl

------------------------------------------------------------------------
-- 4. Concrete same-object payment interface for the toroidal cube.
------------------------------------------------------------------------

record ToroidalCubeImageRecognition
    (CubeImage Face : Set)
    (structure : FaceRecoveryStructure Face) : Set₁ where
  field
    cubeImageToGraph : CubeImage → TwoFaceImageGraph structure
    graphToCubeImage : TwoFaceImageGraph structure → CubeImage
    cubeAfterGraph :
      (graph : TwoFaceImageGraph structure) →
      cubeImageToGraph (graphToCubeImage graph) ≡ graph
    graphAfterCube :
      (cube : CubeImage) →
      graphToCubeImage (cubeImageToGraph cube) ≡ cube

open ToroidalCubeImageRecognition public

------------------------------------------------------------------------
-- 5. Once the concrete face is the existing PhaseFineField, the already-paid
-- two-face weld compiles immediately to Q9 -> Q9.  We keep the final concrete
-- cube-image recognition as an explicit dependent input.
------------------------------------------------------------------------

record CubeImageToQ9FieldRecognition (CubeImage : Set) : Set₁ where
  field
    cubeToTwoFaces : CubeImage → Q9Weld.TwoFineFaces
    twoFacesToCube : Q9Weld.TwoFineFaces → CubeImage
    cubeAfterTwoFaces :
      (faces : Q9Weld.TwoFineFaces) →
      cubeToTwoFaces (twoFacesToCube faces) ≡ faces
    twoFacesAfterCube :
      (cube : CubeImage) →
      twoFacesToCube (cubeToTwoFaces cube) ≡ cube

open CubeImageToQ9FieldRecognition public

cubeToQ9Field :
  ∀ {CubeImage} →
  CubeImageToQ9FieldRecognition CubeImage →
  CubeImage → Q9Weld.Q9Field9
cubeToQ9Field recognition cube =
  Q9Weld.facesToQ9Field (cubeToTwoFaces recognition cube)

q9FieldToCube :
  ∀ {CubeImage} →
  CubeImageToQ9FieldRecognition CubeImage →
  Q9Weld.Q9Field9 → CubeImage
q9FieldToCube recognition field =
  twoFacesToCube recognition (Q9Weld.q9FieldToFaces field)

------------------------------------------------------------------------
-- 6. Characteristic-three derivation obligation.  This is the exact missing
-- same-object weld from the abstract graph theorem to the selected toroidal
-- face operator, not a cardinality check.
------------------------------------------------------------------------

record ConcreteTorusFaceOperatorPayment (Face : Set)
    (structure : FaceRecoveryStructure Face) : Set₁ where
  field
    sxCubedIsIdentity : Set
    syCubedIsIdentity : Set
    sxSyCommute : Set
    characteristicThreeFreshmansDreamPaid : Set
    bCubedIsNegativeIdentity : Set
    actualCubeStepHasThreeLayerEquations : Set
    actualCubeImageEqualsGraphCarrier : Set

record CubeImageRecognitionBoundary : Set where
  constructor cube-image-recognition-boundary
  field
    graphIsExactlyCoordinatedByTwoFaces : Bool
    twoFineFacesExactlyWeldToQ9Field : Bool
    numericalRank18AlonePaysConcreteCubeImageEquality : Bool
    bCubedIdentityIsTheAlgebraicReasonForCancellation : Bool
    equalNinePowerCardinalityIsUsedAsProof : Bool

canonicalCubeImageRecognitionBoundary : CubeImageRecognitionBoundary
canonicalCubeImageRecognitionBoundary =
  cube-image-recognition-boundary
    true true false true false
