module DASHI.Foundations.Base369Situated54FaceIncidence54BridgeExact where

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Completion54SituatedTriadBridgeExact as Completion
import DASHI.Foundations.Base369StableAlgebraicIdentityTowerExact as Stable
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369FaceSheetPunctureIncidenceIdentityExact as Face

------------------------------------------------------------------------
-- SITUATED 54 <-> FACE-INCIDENCE 54
--
-- This is an explicit carrier chart between two separately named 54-state
-- objects.  It does not identify their semantics.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Situated row/column <-> cube face sign/axis.
------------------------------------------------------------------------

situatedSlotToFace : Completion.SituatedSlot → Geometry.Face6
situatedSlotToFace (Completion.situated-slot Completion.observationalRow Completion.firstAxis) = Geometry.xNegativeFace
situatedSlotToFace (Completion.situated-slot Completion.governedRow Completion.firstAxis) = Geometry.xPositiveFace
situatedSlotToFace (Completion.situated-slot Completion.observationalRow Completion.secondAxis) = Geometry.yNegativeFace
situatedSlotToFace (Completion.situated-slot Completion.governedRow Completion.secondAxis) = Geometry.yPositiveFace
situatedSlotToFace (Completion.situated-slot Completion.observationalRow Completion.thirdAxis) = Geometry.zNegativeFace
situatedSlotToFace (Completion.situated-slot Completion.governedRow Completion.thirdAxis) = Geometry.zPositiveFace

faceToSituatedSlot : Geometry.Face6 → Completion.SituatedSlot
faceToSituatedSlot Geometry.xNegativeFace = Completion.situated-slot Completion.observationalRow Completion.firstAxis
faceToSituatedSlot Geometry.xPositiveFace = Completion.situated-slot Completion.governedRow Completion.firstAxis
faceToSituatedSlot Geometry.yNegativeFace = Completion.situated-slot Completion.observationalRow Completion.secondAxis
faceToSituatedSlot Geometry.yPositiveFace = Completion.situated-slot Completion.governedRow Completion.secondAxis
faceToSituatedSlot Geometry.zNegativeFace = Completion.situated-slot Completion.observationalRow Completion.thirdAxis
faceToSituatedSlot Geometry.zPositiveFace = Completion.situated-slot Completion.governedRow Completion.thirdAxis

situatedFaceRoundTrip :
  (slot : Completion.SituatedSlot) →
  faceToSituatedSlot (situatedSlotToFace slot) ≡ slot
situatedFaceRoundTrip (Completion.situated-slot Completion.observationalRow Completion.firstAxis) = refl
situatedFaceRoundTrip (Completion.situated-slot Completion.governedRow Completion.firstAxis) = refl
situatedFaceRoundTrip (Completion.situated-slot Completion.observationalRow Completion.secondAxis) = refl
situatedFaceRoundTrip (Completion.situated-slot Completion.governedRow Completion.secondAxis) = refl
situatedFaceRoundTrip (Completion.situated-slot Completion.observationalRow Completion.thirdAxis) = refl
situatedFaceRoundTrip (Completion.situated-slot Completion.governedRow Completion.thirdAxis) = refl

faceSituatedRoundTrip :
  (face : Geometry.Face6) →
  situatedSlotToFace (faceToSituatedSlot face) ≡ face
faceSituatedRoundTrip Geometry.xNegativeFace = refl
faceSituatedRoundTrip Geometry.xPositiveFace = refl
faceSituatedRoundTrip Geometry.yNegativeFace = refl
faceSituatedRoundTrip Geometry.yPositiveFace = refl
faceSituatedRoundTrip Geometry.zNegativeFace = refl
faceSituatedRoundTrip Geometry.zPositiveFace = refl

situated6IsFace6 :
  Stable.CarrierIso Completion.SituatedSlot Geometry.Face6
situated6IsFace6 =
  Stable.carrier-iso
    situatedSlotToFace
    faceToSituatedSlot
    situatedFaceRoundTrip
    faceSituatedRoundTrip

------------------------------------------------------------------------
-- 2. Comparison nonary <-> local face sheet.
------------------------------------------------------------------------

nonaryToFaceSheet : Stable.Nonary9 → Face.FaceSheet9
nonaryToFaceSheet (Base.tri-mid , Base.tri-mid) = Face.faceCentre
nonaryToFaceSheet (Base.tri-low , Base.tri-low) = Face.facePuncture Face.negNeg
nonaryToFaceSheet (Base.tri-low , Base.tri-mid) = Face.facePuncture Face.negZero
nonaryToFaceSheet (Base.tri-low , Base.tri-high) = Face.facePuncture Face.negPos
nonaryToFaceSheet (Base.tri-mid , Base.tri-low) = Face.facePuncture Face.zeroNeg
nonaryToFaceSheet (Base.tri-mid , Base.tri-high) = Face.facePuncture Face.zeroPos
nonaryToFaceSheet (Base.tri-high , Base.tri-low) = Face.facePuncture Face.posNeg
nonaryToFaceSheet (Base.tri-high , Base.tri-mid) = Face.facePuncture Face.posZero
nonaryToFaceSheet (Base.tri-high , Base.tri-high) = Face.facePuncture Face.posPos

faceSheetToNonary : Face.FaceSheet9 → Stable.Nonary9
faceSheetToNonary Face.faceCentre = Base.tri-mid , Base.tri-mid
faceSheetToNonary (Face.facePuncture Face.negNeg) = Base.tri-low , Base.tri-low
faceSheetToNonary (Face.facePuncture Face.negZero) = Base.tri-low , Base.tri-mid
faceSheetToNonary (Face.facePuncture Face.negPos) = Base.tri-low , Base.tri-high
faceSheetToNonary (Face.facePuncture Face.zeroNeg) = Base.tri-mid , Base.tri-low
faceSheetToNonary (Face.facePuncture Face.zeroPos) = Base.tri-mid , Base.tri-high
faceSheetToNonary (Face.facePuncture Face.posNeg) = Base.tri-high , Base.tri-low
faceSheetToNonary (Face.facePuncture Face.posZero) = Base.tri-high , Base.tri-mid
faceSheetToNonary (Face.facePuncture Face.posPos) = Base.tri-high , Base.tri-high

nonaryFaceSheetRoundTrip :
  (n : Stable.Nonary9) → faceSheetToNonary (nonaryToFaceSheet n) ≡ n
nonaryFaceSheetRoundTrip (Base.tri-low , Base.tri-low) = refl
nonaryFaceSheetRoundTrip (Base.tri-low , Base.tri-mid) = refl
nonaryFaceSheetRoundTrip (Base.tri-low , Base.tri-high) = refl
nonaryFaceSheetRoundTrip (Base.tri-mid , Base.tri-low) = refl
nonaryFaceSheetRoundTrip (Base.tri-mid , Base.tri-mid) = refl
nonaryFaceSheetRoundTrip (Base.tri-mid , Base.tri-high) = refl
nonaryFaceSheetRoundTrip (Base.tri-high , Base.tri-low) = refl
nonaryFaceSheetRoundTrip (Base.tri-high , Base.tri-mid) = refl
nonaryFaceSheetRoundTrip (Base.tri-high , Base.tri-high) = refl

faceSheetNonaryRoundTrip :
  (sheet : Face.FaceSheet9) → nonaryToFaceSheet (faceSheetToNonary sheet) ≡ sheet
faceSheetNonaryRoundTrip Face.faceCentre = refl
faceSheetNonaryRoundTrip (Face.facePuncture Face.negNeg) = refl
faceSheetNonaryRoundTrip (Face.facePuncture Face.negZero) = refl
faceSheetNonaryRoundTrip (Face.facePuncture Face.negPos) = refl
faceSheetNonaryRoundTrip (Face.facePuncture Face.zeroNeg) = refl
faceSheetNonaryRoundTrip (Face.facePuncture Face.zeroPos) = refl
faceSheetNonaryRoundTrip (Face.facePuncture Face.posNeg) = refl
faceSheetNonaryRoundTrip (Face.facePuncture Face.posZero) = refl
faceSheetNonaryRoundTrip (Face.facePuncture Face.posPos) = refl

nonary9IsFaceSheet9 : Stable.CarrierIso Stable.Nonary9 Face.FaceSheet9
nonary9IsFaceSheet9 =
  Stable.carrier-iso
    nonaryToFaceSheet
    faceSheetToNonary
    nonaryFaceSheetRoundTrip
    faceSheetNonaryRoundTrip

------------------------------------------------------------------------
-- 3. Product transport gives situated completion 54 <-> face incidence 54.
------------------------------------------------------------------------

situated54ToFaceIncidence54 : Stable.Completion54 → Face.FaceIncidence54
situated54ToFaceIncidence54 (slot , nonary) =
  situatedSlotToFace slot , nonaryToFaceSheet nonary

faceIncidence54ToSituated54 : Face.FaceIncidence54 → Stable.Completion54
faceIncidence54ToSituated54 (face , sheet) =
  faceToSituatedSlot face , faceSheetToNonary sheet

situated54FaceRoundTrip :
  (state : Stable.Completion54) →
  faceIncidence54ToSituated54 (situated54ToFaceIncidence54 state) ≡ state
situated54FaceRoundTrip (slot , nonary)
  rewrite situatedFaceRoundTrip slot
        | nonaryFaceSheetRoundTrip nonary = refl

faceSituated54RoundTrip :
  (state : Face.FaceIncidence54) →
  situated54ToFaceIncidence54 (faceIncidence54ToSituated54 state) ≡ state
faceSituated54RoundTrip (face , sheet)
  rewrite faceSituatedRoundTrip face
        | faceSheetNonaryRoundTrip sheet = refl

situated54IsFaceIncidence54 :
  Stable.CarrierIso Stable.Completion54 Face.FaceIncidence54
situated54IsFaceIncidence54 =
  Stable.carrier-iso
    situated54ToFaceIncidence54
    faceIncidence54ToSituated54
    situated54FaceRoundTrip
    faceSituated54RoundTrip

------------------------------------------------------------------------
-- 4. Boundaries.
------------------------------------------------------------------------

data SituatedRowSemanticallyEqualsFaceSign : Set where
data SituatedColumnSemanticallyEqualsSpatialAxis : Set where
data ComparisonNonarySemanticallyEqualsGeometricFace : Set where
data CarrierChartCreatesMonsterGeometrySemantics : Set where

rowFaceBridgeIsCarrierOnly : SituatedRowSemanticallyEqualsFaceSign → ⊥
rowFaceBridgeIsCarrierOnly ()

columnAxisBridgeIsCarrierOnly : SituatedColumnSemanticallyEqualsSpatialAxis → ⊥
columnAxisBridgeIsCarrierOnly ()

nonaryFaceBridgeIsCarrierOnly : ComparisonNonarySemanticallyEqualsGeometricFace → ⊥
nonaryFaceBridgeIsCarrierOnly ()

carrierChartDoesNotCreateMonsterGeometrySemantics :
  CarrierChartCreatesMonsterGeometrySemantics → ⊥
carrierChartDoesNotCreateMonsterGeometrySemantics ()

record Situated54FaceIncidenceBoundary : Set where
  constructor situated54-face-incidence-boundary
  field
    situatedSixBridgedToSixFaces : Bool
    comparisonNineBridgedToFaceNine : Bool
    situated54BridgedToFaceIncidence54 : Bool
    bridgeIsSemanticIdentity : Bool
    bridgeCreatesMonsterAction : Bool

canonicalSituated54FaceIncidenceBoundary : Situated54FaceIncidenceBoundary
canonicalSituated54FaceIncidenceBoundary =
  situated54-face-incidence-boundary true true true false false
