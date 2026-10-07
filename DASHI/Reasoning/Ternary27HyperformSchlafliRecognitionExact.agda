module DASHI.Reasoning.Ternary27HyperformSchlafliRecognitionExact where

------------------------------------------------------------------------
-- TYPED TERNARY-27 HYPERVOXEL -> SIX+FIFTEEN+SIX SCHLAEFLI CHART
--
-- The additive F3^3 Cayley obstruction forgets the absolute typed geometry of
-- the existing Ternary27Point.  This owner keeps that geometry and gives an
-- explicit two-sided chart into the classical Schlaefli 6+15+6 carrier.
--
-- Provenance of the chart:
--   * six face centres -> left six oriented faces;
--   * twelve edge centres -> twelve non-opposite face pairs;
--   * origin + the two named diagonal corners -> three opposite face pairs;
--   * remaining six corners -> right six, indexed by the unique minority
--     signed coordinate.
--
-- The companion Lean finite producer proves that the induced relation is
-- SRG(27,16,10,8), its complement is SRG(27,10,1,5), and the chart is
-- relation-level same-object with the paid E6 omega5 minuscule orbit.
-- This Agda file pays the literal carrier/chart bijection and types the
-- cross-kernel relation/action receipts without importing Lean authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Strata

------------------------------------------------------------------------
-- 1. Fifteen unordered pairs of the six existing oriented cube faces.
------------------------------------------------------------------------

data FacePair15 : Set where
  xOpp yOpp zOpp : FacePair15
  xNegYNeg xNegYPos xPosYNeg xPosYPos : FacePair15
  xNegZNeg xNegZPos xPosZNeg xPosZPos : FacePair15
  yNegZNeg yNegZPos yPosZNeg yPosZPos : FacePair15

facePairCount : Nat
facePairCount = 15

------------------------------------------------------------------------
-- 2. Classical 6 + 15 + 6 carrier, retaining left/right provenance.
------------------------------------------------------------------------

data Schlafli27Label : Set where
  leftFace : Geometry.Face6 → Schlafli27Label
  middlePair : FacePair15 → Schlafli27Label
  rightFace : Geometry.Face6 → Schlafli27Label

leftSixCount : Nat
leftSixCount = 6

rightSixCount : Nat
rightSixCount = 6

schlafliChartCount : Nat
schlafliChartCount = leftSixCount + facePairCount + rightSixCount

schlafliChartCountIs27 : schlafliChartCount ≡ 27
schlafliChartCountIs27 = refl

------------------------------------------------------------------------
-- 3. Literal raw-ternary -> 6+15+6 chart.
------------------------------------------------------------------------

pointToSchlafliLabel : Geometry.Ternary27Point → Schlafli27Label
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne) = middlePair yOpp
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero) = middlePair xNegYNeg
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne) = rightFace Geometry.zPositiveFace
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne) = middlePair xNegZNeg
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero) = leftFace Geometry.xNegativeFace
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne) = middlePair xNegZPos
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne) = rightFace Geometry.yPositiveFace
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero) = middlePair xNegYPos
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne) = rightFace Geometry.xNegativeFace
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne) = middlePair yNegZNeg
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero) = leftFace Geometry.yNegativeFace
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne) = middlePair yNegZPos
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne) = leftFace Geometry.zNegativeFace
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero) = middlePair xOpp
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne) = leftFace Geometry.zPositiveFace
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne) = middlePair yPosZNeg
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero) = leftFace Geometry.yPositiveFace
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne) = middlePair yPosZPos
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne) = rightFace Geometry.xPositiveFace
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero) = middlePair xPosYNeg
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne) = rightFace Geometry.yNegativeFace
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne) = middlePair xPosZNeg
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero) = leftFace Geometry.xPositiveFace
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne) = middlePair xPosZPos
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne) = rightFace Geometry.zNegativeFace
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero) = middlePair xPosYPos
pointToSchlafliLabel (Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne) = middlePair zOpp

------------------------------------------------------------------------
-- 4. Explicit inverse.
------------------------------------------------------------------------

leftFacePoint : Geometry.Face6 → Geometry.Ternary27Point
leftFacePoint Geometry.xNegativeFace = Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero
leftFacePoint Geometry.xPositiveFace = Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero
leftFacePoint Geometry.yNegativeFace = Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero
leftFacePoint Geometry.yPositiveFace = Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero
leftFacePoint Geometry.zNegativeFace = Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne
leftFacePoint Geometry.zPositiveFace = Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne

rightFacePoint : Geometry.Face6 → Geometry.Ternary27Point
rightFacePoint Geometry.xNegativeFace = Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne
rightFacePoint Geometry.xPositiveFace = Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne
rightFacePoint Geometry.yNegativeFace = Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne
rightFacePoint Geometry.yPositiveFace = Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne
rightFacePoint Geometry.zNegativeFace = Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne
rightFacePoint Geometry.zPositiveFace = Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne

middlePairPoint : FacePair15 → Geometry.Ternary27Point
middlePairPoint xOpp = Geometry.origin
middlePairPoint yOpp = Geometry.negativeCorner
middlePairPoint zOpp = Geometry.positiveCorner
middlePairPoint xNegYNeg = Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero
middlePairPoint xNegYPos = Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero
middlePairPoint xPosYNeg = Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero
middlePairPoint xPosYPos = Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero
middlePairPoint xNegZNeg = Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne
middlePairPoint xNegZPos = Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne
middlePairPoint xPosZNeg = Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne
middlePairPoint xPosZPos = Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne
middlePairPoint yNegZNeg = Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne
middlePairPoint yNegZPos = Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne
middlePairPoint yPosZNeg = Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne
middlePairPoint yPosZPos = Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne

schlafliLabelToPoint : Schlafli27Label → Geometry.Ternary27Point
schlafliLabelToPoint (leftFace f) = leftFacePoint f
schlafliLabelToPoint (middlePair p) = middlePairPoint p
schlafliLabelToPoint (rightFace f) = rightFacePoint f

pointAfterLabel : (p : Geometry.Ternary27Point) →
  schlafliLabelToPoint (pointToSchlafliLabel p) ≡ p
pointAfterLabel (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspNegOne) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspZero) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspNegOne SSP.sspNegOne SSP.sspPosOne) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspNegOne) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspZero) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspNegOne SSP.sspZero SSP.sspPosOne) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspNegOne) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspZero) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspNegOne SSP.sspPosOne SSP.sspPosOne) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspNegOne) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspZero) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspZero SSP.sspNegOne SSP.sspPosOne) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspNegOne) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspZero SSP.sspZero SSP.sspPosOne) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspNegOne) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspZero) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspZero SSP.sspPosOne SSP.sspPosOne) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspNegOne) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspZero) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspPosOne SSP.sspNegOne SSP.sspPosOne) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspNegOne) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspZero) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspPosOne SSP.sspZero SSP.sspPosOne) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspNegOne) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspZero) = refl
pointAfterLabel (Geometry.ternary27Point SSP.sspPosOne SSP.sspPosOne SSP.sspPosOne) = refl

labelAfterPoint : (l : Schlafli27Label) →
  pointToSchlafliLabel (schlafliLabelToPoint l) ≡ l
labelAfterPoint (leftFace Geometry.xNegativeFace) = refl
labelAfterPoint (leftFace Geometry.xPositiveFace) = refl
labelAfterPoint (leftFace Geometry.yNegativeFace) = refl
labelAfterPoint (leftFace Geometry.yPositiveFace) = refl
labelAfterPoint (leftFace Geometry.zNegativeFace) = refl
labelAfterPoint (leftFace Geometry.zPositiveFace) = refl
labelAfterPoint (middlePair xOpp) = refl
labelAfterPoint (middlePair yOpp) = refl
labelAfterPoint (middlePair zOpp) = refl
labelAfterPoint (middlePair xNegYNeg) = refl
labelAfterPoint (middlePair xNegYPos) = refl
labelAfterPoint (middlePair xPosYNeg) = refl
labelAfterPoint (middlePair xPosYPos) = refl
labelAfterPoint (middlePair xNegZNeg) = refl
labelAfterPoint (middlePair xNegZPos) = refl
labelAfterPoint (middlePair xPosZNeg) = refl
labelAfterPoint (middlePair xPosZPos) = refl
labelAfterPoint (middlePair yNegZNeg) = refl
labelAfterPoint (middlePair yNegZPos) = refl
labelAfterPoint (middlePair yPosZNeg) = refl
labelAfterPoint (middlePair yPosZPos) = refl
labelAfterPoint (rightFace Geometry.xNegativeFace) = refl
labelAfterPoint (rightFace Geometry.xPositiveFace) = refl
labelAfterPoint (rightFace Geometry.yNegativeFace) = refl
labelAfterPoint (rightFace Geometry.yPositiveFace) = refl
labelAfterPoint (rightFace Geometry.zNegativeFace) = refl
labelAfterPoint (rightFace Geometry.zPositiveFace) = refl

------------------------------------------------------------------------
-- 5. Typed finite-relation and A5/S6 receipt surfaces.
------------------------------------------------------------------------

record Ternary27SchlafliRelationReceipt : Set₁ where
  field
    related : Geometry.Ternary27Point → Geometry.Ternary27Point → Set
    degree16 : Set
    adjacentCommon10 : Set
    nonAdjacentCommon8 : Set
    orthogonalDegree10 : Set
    orthogonalAdjacentCommon1 : Set
    orthogonalNonAdjacentCommon5 : Set
    minusculeCarrierSameObjectReceipt : Set
    minusculeRelationIntertwinerReceipt : Set
open Ternary27SchlafliRelationReceipt public

record A5SixObjectActionReceipt : Set₁ where
  field
    SixObject : Set
    Actor : Set
    act : Actor → SixObject → SixObject
    sixObjectIsExistingFaceType : Set
    fiveA5GeneratorsTyped : Set
    generatedActionHas720Elements : Set
    generatedActionIsAllSixObjectPermutations : Set
open A5SixObjectActionReceipt public

record IndependentRawTernaryE6ActionReceipt
  (S : Ternary27SchlafliRelationReceipt) : Set₁ where
  field
    E6Actor : Set
    action : E6Actor → Geometry.Ternary27Point → Geometry.Ternary27Point
    preservesSchlafliRelation : Set
    intertwinesExistingHyperformOperations : Set
open IndependentRawTernaryE6ActionReceipt public

record Ternary27HyperformSchlafliBoundary : Set where
  constructor ternary27-hyperform-schlafli-boundary
  field
    usesExistingTernary27Point : Bool
    usesExistingSixOrientedFaces : Bool
    exactSixPlusFifteenPlusSixChartPaid : Bool
    chartTwoSidedBijectionPaidInAgda : Bool
    leanSchlafliSRGProducerSourceWritten : Bool
    leanMinusculeRelationIntertwinerSourceWritten : Bool
    leanA5SixObjectS6ProducerSourceWritten : Bool
    additiveTranslationInvarianceRequired : Bool
    independentRawTernaryE6ActionPaid : Bool
    albertJordanProductPaid : Bool
    agdaSRGEnumerationKernelPaidHere : Bool
    nextResidual : String
open Ternary27HyperformSchlafliBoundary public

canonicalTernary27HyperformSchlafliBoundary : Ternary27HyperformSchlafliBoundary
canonicalTernary27HyperformSchlafliBoundary =
  ternary27-hyperform-schlafli-boundary
    true true true true
    true true true
    false false false false
    "The raw ternary 27 now has a literal absolute 6+15+6 hypervoxel chart. Companion Lean source proves that the induced non-Cayley relation is SRG(27,16,10,8) and equals the E6 omega5 minuscule pairing relation. Remaining promotion gate: independently derive/intertwine the E6 action from the pre-existing hyperfabric/pants operations rather than defining it only by transport; Albert product/unit/cubic norm/F4 remain stronger algebra data."
