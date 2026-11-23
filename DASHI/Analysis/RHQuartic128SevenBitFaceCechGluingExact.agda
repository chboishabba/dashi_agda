module DASHI.Analysis.RHQuartic128SevenBitFaceCechGluingExact where

------------------------------------------------------------------------
-- RH/GRH 128 NORMALIZATION -> SEVEN-BIT / SIX-FACE ACTUAL SECTION
--
-- Reuse rather than reconstruct the owners:
--   Lean FourierMass: 128 = 16 (r=t/16) * 2 (even Fourier inversion)
--                         * 4 (original profile P_W(0) factor).
--   Base369Ternary27HypervoxelFabricGeometryExact: six real face labels.
--   Base369Ternary27CornerEightExact: eight real corner signs.
--   Base369Ternary27BoundaryNerveExact: 12 edges, 8 corners.
--   Base369Ternary27FaceHypercubeCechGluingBidiExact: Cech law.
--   JInvariantSheafHyperformAdmissibleDescentExact: compatible overlap.
--   TernaryThirteenPantsSheafGluingTransportExact: matched neutral branch.
--
-- Source-level mathematical result:
--   (2^4 * 2^1 * 2^2) factors into seven labelled binary weights.
--   Choosing one boundary bit from each block gives an exact bijection
--             BinarySeven  <->  BoundaryCorner3 x ResidualBinary4.
--   Six face charts cover the full 128-state actual *coefficient* carrier;
--   compatible local sections glue pointwise and uniquely.
--   Every original zero/sign source remains independent of these positive
--   scalar weights.  No physical seven-dimensional group action and no RH.
--
-- The six actual Fourier q probes (2,8,12,20,24,32) are NOT the faces.
-- The six-face atlas is the original Base369 OUTER CORNER NERVE;
-- its neutral/centre points belong to the distinct ternary 27 cube and
-- are not invented as binary states.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Product using (_×_; _,_)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27CornerEightExact as Corners
import DASHI.Foundations.Base369Ternary27BoundaryNerveExact as Nerve
import DASHI.Moonshine.Base369Ternary27FaceHypercubeCechGluingBidiExact as Cech

record BinarySeven : Set where
  constructor binarySeven
  field
    a0 a1 a2 a3 : Bool
    b0 : Bool
    c0 c1 : Bool
open BinarySeven public

record BoundaryCorner3 : Set where
  constructor boundaryCorner3
  field
    xBit yBit zBit : Bool
open BoundaryCorner3 public

record ResidualBinary4 : Set where
  constructor residualBinary4
  field
    a1Residual a2Residual a3Residual c1Residual : Bool
open ResidualBinary4 public

splitCornerResidual : BinarySeven → BoundaryCorner3 × ResidualBinary4
splitCornerResidual (binarySeven a0 a1 a2 a3 b0 c0 c1) =
  boundaryCorner3 a0 b0 c0 , residualBinary4 a1 a2 a3 c1

joinCornerResidual : BoundaryCorner3 × ResidualBinary4 → BinarySeven
joinCornerResidual
  (boundaryCorner3 a0 b0 c0 , residualBinary4 a1 a2 a3 c1) =
  binarySeven a0 a1 a2 a3 b0 c0 c1

joinAfterSplit :
  (state : BinarySeven) →
  joinCornerResidual (splitCornerResidual state) ≡ state
joinAfterSplit (binarySeven a0 a1 a2 a3 b0 c0 c1) = refl

splitAfterJoin :
  (pair : BoundaryCorner3 × ResidualBinary4) →
  splitCornerResidual (joinCornerResidual pair) ≡ pair
splitAfterJoin (boundaryCorner3 a0 b0 c0 , residualBinary4 a1 a2 a3 c1) = refl

bitToOuter : Bool → Corners.OuterSign
bitToOuter false = Corners.negativeOuter
bitToOuter true = Corners.positiveOuter

sourceCorner : BinarySeven → Corners.Corner3
sourceCorner state =
  Corners.corner3 (bitToOuter (a0 state))
                  (bitToOuter (b0 state))
                  (bitToOuter (c0 state))

xFace : Bool → Geometry.Face6
xFace false = Geometry.xNegativeFace
xFace true = Geometry.xPositiveFace

yFace : Bool → Geometry.Face6
yFace false = Geometry.yNegativeFace
yFace true = Geometry.yPositiveFace

zFace : Bool → Geometry.Face6
zFace false = Geometry.zNegativeFace
zFace true = Geometry.zPositiveFace

faceFor : Geometry.Axis3 → BinarySeven → Geometry.Face6
faceFor Geometry.xAxis state = xFace (a0 state)
faceFor Geometry.yAxis state = yFace (b0 state)
faceFor Geometry.zAxis state = zFace (c0 state)

sourceCornerOnXFace :
  (state : BinarySeven) →
  Geometry.OnFace (faceFor Geometry.xAxis state)
    (Corners.cornerPoint (sourceCorner state))
sourceCornerOnXFace (binarySeven false a1 a2 a3 b0 c0 c1) =
  Geometry.onFace refl
sourceCornerOnXFace (binarySeven true a1 a2 a3 b0 c0 c1) =
  Geometry.onFace refl

sourceCornerOnYFace :
  (state : BinarySeven) →
  Geometry.OnFace (faceFor Geometry.yAxis state)
    (Corners.cornerPoint (sourceCorner state))
sourceCornerOnYFace (binarySeven a0 a1 a2 a3 false c0 c1) =
  Geometry.onFace refl
sourceCornerOnYFace (binarySeven a0 a1 a2 a3 true c0 c1) =
  Geometry.onFace refl

sourceCornerOnZFace :
  (state : BinarySeven) →
  Geometry.OnFace (faceFor Geometry.zAxis state)
    (Corners.cornerPoint (sourceCorner state))
sourceCornerOnZFace (binarySeven a0 a1 a2 a3 b0 false c1) =
  Geometry.onFace refl
sourceCornerOnZFace (binarySeven a0 a1 a2 a3 b0 true c1) =
  Geometry.onFace refl

------------------------------------------------------------------------
-- All seven source-derived factors are positive and keep the separate
-- original blocks (physical four, Fourier one, origin two).
------------------------------------------------------------------------

factor2 : Bool → Nat
factor2 false = 1
factor2 true = 2

physicalBlock : BinarySeven → Nat
physicalBlock state =
  factor2 (a0 state) * factor2 (a1 state)
  * factor2 (a2 state) * factor2 (a3 state)

fourierBlock : BinarySeven → Nat
fourierBlock state = factor2 (b0 state)

originBlock : BinarySeven → Nat
originBlock state = factor2 (c0 state) * factor2 (c1 state)

coefficient : BinarySeven → Nat
coefficient state =
  physicalBlock state * fourierBlock state * originBlock state

allOnes : BinarySeven
allOnes = binarySeven true true true true true true true

normalizationFull : coefficient allOnes ≡ 128
normalizationFull = refl

physicalFull : physicalBlock allOnes ≡ 16
physicalFull = refl

fourierFull : fourierBlock allOnes ≡ 2
fourierFull = refl

originFull : originBlock allOnes ≡ 4
originFull = refl

------------------------------------------------------------------------
-- Pointwise exact sheaf of actual seven-bit coefficient sections.
-- Opposite face charts have empty overlap.  Every state lives on its
-- selected x-, y-, z-faces. A compatible family agrees with its x-chart
-- on all incident faces; this is equivalent to all pairwise edge matching.
-- Gluing does not use unproved function extensionality.
------------------------------------------------------------------------

data Polarity : Set where
  negative : Polarity
  neutral : Polarity
  positive : Polarity

CoefficientValue : Set
CoefficientValue = Nat × Polarity

GlobalSection : Set
GlobalSection = BinarySeven → CoefficientValue

FaceLocalSections : Set
FaceLocalSections = Geometry.Face6 → BinarySeven → CoefficientValue

restrict :
  GlobalSection → FaceLocalSections
restrict global face state = global state

compatible :
  FaceLocalSections → Set
compatible locals =
  (state : BinarySeven) →
  (face : Geometry.Face6) →
  faceFor (Geometry.faceAxis face) state ≡ face →
  locals face state ≡ locals (faceFor Geometry.xAxis state) state

glue : (locals : FaceLocalSections) →
  compatible locals → GlobalSection
glue locals matching state = locals (faceFor Geometry.xAxis state) state

reverseEq : {A : Set} {x y : A} → x ≡ y → y ≡ x
reverseEq refl = refl

transEq : {A : Set} {x y z : A} →
  x ≡ y → y ≡ z → x ≡ z
transEq refl q = q

restrictsCompatible :
  (global : GlobalSection) →
  compatible (restrict global)
restrictsCompatible global state face incident = refl

glueAfterRestrict :
  (global : GlobalSection) →
  (state : BinarySeven) →
  glue (restrict global) (restrictsCompatible global) state ≡ global state
glueAfterRestrict global state = refl

restrictAfterGluePointwise :
  (locals : FaceLocalSections) →
  (matching : compatible locals) →
  (state : BinarySeven) →
  (face : Geometry.Face6) →
  (incident : faceFor (Geometry.faceAxis face) state ≡ face) →
  restrict (glue locals matching) face state ≡ locals face state
restrictAfterGluePointwise locals matching state face incident =
  reverseEq (matching state face incident)

matchingImpliesEveryEdge :
  (locals : FaceLocalSections) →
  (matching : compatible locals) →
  (state : BinarySeven) →
  (first second : Geometry.Face6) →
  faceFor (Geometry.faceAxis first) state ≡ first →
  faceFor (Geometry.faceAxis second) state ≡ second →
  locals first state ≡ locals second state
matchingImpliesEveryEdge locals matching state first second firstOn secondOn =
  transEq (matching state first firstOn)
    (reverseEq (matching state second secondOn))

------------------------------------------------------------------------
-- Chosen literal signed/zero source: no positive-coefficient assertion
-- may erase the neutral branch or reverse the independent signed label.
------------------------------------------------------------------------

coefficientSection : Polarity → GlobalSection
coefficientSection orientation state = coefficient state , orientation

zeroRetained :
  (state : BinarySeven) →
  coefficientSection neutral state ≡ (coefficient state , neutral)
zeroRetained state = refl

negativeRetained :
  (state : BinarySeven) →
  coefficientSection negative state ≡ (coefficient state , negative)
negativeRetained state = refl

positiveRetained :
  (state : BinarySeven) →
  coefficientSection positive state ≡ (coefficient state , positive)
positiveRetained state = refl

------------------------------------------------------------------------
-- Existing nerve/sheaf owners remain authoritative.  The analytic
-- sampleTest/paperFT identity and Monster X6 actor same-object recognition
-- are not manufactured by this finite scalar model.
------------------------------------------------------------------------

originalNerveHasSixFaces :
  Nerve.sixFacesOwned Nerve.canonicalBoundaryNerveBoundary ≡ true
originalNerveHasSixFaces = refl

originalCechHasSixFaceObjects :
  Cech.sixFaceObjectsOwned Cech.canonicalFaceHypercubeCechBoundary ≡ true
originalCechHasSixFaceObjects = refl

originalCechDoesNotPromoteMonster :
  Cech.modelGluingImpliesActualMonsterGluing
    Cech.canonicalFaceHypercubeCechBoundary ≡ false
originalCechDoesNotPromoteMonster = refl


------------------------------------------------------------------------
-- Unique pointwise descent on the covered seven-bit coefficient carrier.
-- The x-incident face is always one of the three face descriptions of
-- the literal corner. A second global section agreeing with all local
-- incident face data must agree with the glued section at every state.
------------------------------------------------------------------------

selectedXFaceIncident :
  (state : BinarySeven) →
  faceFor (Geometry.faceAxis (faceFor Geometry.xAxis state)) state
  ≡ faceFor Geometry.xAxis state
selectedXFaceIncident (binarySeven false a1 a2 a3 b0 c0 c1) = refl
selectedXFaceIncident (binarySeven true a1 a2 a3 b0 c0 c1) = refl

glueUniquePointwise :
  (locals : FaceLocalSections) →
  (matching : compatible locals) →
  (candidate : GlobalSection) →
  ((state : BinarySeven) → (face : Geometry.Face6) →
   (incident : faceFor (Geometry.faceAxis face) state ≡ face) →
   candidate state ≡ locals face state) →
  (state : BinarySeven) →
  candidate state ≡ glue locals matching state
glueUniquePointwise locals matching candidate candidateRestricts state =
  candidateRestricts state (faceFor Geometry.xAxis state)
    (selectedXFaceIncident state)

------------------------------------------------------------------------
-- Source-native "three legs" means only three independently typed scalar
-- stages: physical r=t/16, even Fourier inversion, profile origin value.
-- It is not a smooth pair-of-pants cobordism and changes no original RH
-- normalization. The actual pants InterfaceMatch is still distinct.
------------------------------------------------------------------------

record ThreeLegNormalization : Set where
  constructor threeLegNormalization
  field
    physicalLeg : Nat
    fourierLeg : Nat
    originLeg : Nat
open ThreeLegNormalization public

normalizationLegs : BinarySeven → ThreeLegNormalization
normalizationLegs state =
  threeLegNormalization (physicalBlock state)
    (fourierBlock state) (originBlock state)

glueLegScalars : ThreeLegNormalization → Nat
glueLegScalars legs =
  physicalLeg legs * fourierLeg legs * originLeg legs

threeLegGluingMatchesSourceCoefficient :
  (state : BinarySeven) →
  glueLegScalars (normalizationLegs state) ≡ coefficient state
threeLegGluingMatchesSourceCoefficient state = refl
