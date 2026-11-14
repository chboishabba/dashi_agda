module DASHI.Reasoning.Ternary27HeisenbergThirteenSchlafliBridgeExact where

------------------------------------------------------------------------
-- TERNARY-27 / SCHLAEFLI 6+15+6 / HEISENBERG 3^(1+12) BRIDGE
--
-- The repository already owns, independently:
--
--   * the same raw Ternary27Point with an absolute Schlaefli 6+15+6 chart;
--   * six literal outer faces Face6;
--   * a two-sided Face6 <-> Axis6 chart into X6 = F3^6;
--   * the finite Heisenberg carrier H6 = X6 x X6* x F3;
--   * six translation basis directions and six modulation basis directions.
--
-- This owner makes the 13 = 1 + 6 + 6 and 27 = 6 + 15 + 6 alignments typed,
-- without identifying the central C3 phase with a Schlaefli vertex and without
-- manufacturing a normalizer/E6 action that is not yet source-native.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Data.Product using (_×_; _,_)

import DASHI.Algebra.Trit as Trit
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Base369Ternary27FaceHypercubeAttachmentBidiExact as FaceAxis
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Reasoning.Ternary27HyperformSchlafliRecognitionExact as Schlafli

------------------------------------------------------------------------
-- 1. 13 = 1 + 6 + 6 is role data: centre + position + modulation.
------------------------------------------------------------------------

centralPhaseCoordinateCount : Nat
centralPhaseCoordinateCount = 1

translationAxisCount : Nat
translationAxisCount = 6

modulationAxisCount : Nat
modulationAxisCount = 6

symplecticQuotientCoordinateCount : Nat
symplecticQuotientCoordinateCount = translationAxisCount + modulationAxisCount

extraspecialCoordinateCount : Nat
extraspecialCoordinateCount = centralPhaseCoordinateCount + symplecticQuotientCoordinateCount

symplecticQuotientCoordinateCountIs12 : symplecticQuotientCoordinateCount ≡ 12
symplecticQuotientCoordinateCountIs12 = refl

extraspecialCoordinateCountIs13 : extraspecialCoordinateCount ≡ 13
extraspecialCoordinateCountIs13 = refl

-- Two typed copies of the same six coordinate labels.
data HeisenbergSixRole : Set where
  translationRole : G.Axis6 → HeisenbergSixRole
  modulationRole : G.Axis6 → HeisenbergSixRole

translationRoleBasis : G.Axis6 → H.Symplectic12
translationRoleBasis = H.translationBasis

modulationRoleBasis : G.Axis6 → H.Symplectic12
modulationRoleBasis = H.modulationBasis

canonicalDualPairNontrivial :
  (axis : G.Axis6) →
  H.symplecticPair (translationRoleBasis axis) (modulationRoleBasis axis)
  ≡ Trit.pos
canonicalDualPairNontrivial = H.canonicalBasisPairIsNontrivial

------------------------------------------------------------------------
-- 2. The six hypervoxel faces are already the six X6 translation axes.
--    The same six labels index the modulation/dual copy.
------------------------------------------------------------------------

faceToTranslationAxis : Geometry.Face6 → G.Axis6
faceToTranslationAxis = FaceAxis.faceToAxis6

faceToModulationAxis : Geometry.Face6 → G.Axis6
faceToModulationAxis = FaceAxis.faceToAxis6

translationAxisToFace : G.Axis6 → Geometry.Face6
translationAxisToFace = FaceAxis.axis6ToFace

modulationAxisToFace : G.Axis6 → Geometry.Face6
modulationAxisToFace = FaceAxis.axis6ToFace

translationFaceRoundTrip :
  (face : Geometry.Face6) → translationAxisToFace (faceToTranslationAxis face) ≡ face
translationFaceRoundTrip = FaceAxis.axisAfterFace

modulationFaceRoundTrip :
  (face : Geometry.Face6) → modulationAxisToFace (faceToModulationAxis face) ≡ face
modulationFaceRoundTrip = FaceAxis.axisAfterFace

translationAxisRoundTrip :
  (axis : G.Axis6) → faceToTranslationAxis (translationAxisToFace axis) ≡ axis
translationAxisRoundTrip = FaceAxis.faceAfterAxis

modulationAxisRoundTrip :
  (axis : G.Axis6) → faceToModulationAxis (modulationAxisToFace axis) ≡ axis
modulationAxisRoundTrip = FaceAxis.faceAfterAxis

------------------------------------------------------------------------
-- 3. Fifteen middle labels are literal unordered pairs of the same six axes.
--    This is the finite basis shape of Lambda^2(6); no vector-space exterior
--    algebra is inferred merely from the pair carrier.
------------------------------------------------------------------------

pairAxes : Schlafli.FacePair15 → G.Axis6 × G.Axis6
pairAxes Schlafli.xOpp = G.axis0 , G.axis1
pairAxes Schlafli.yOpp = G.axis2 , G.axis3
pairAxes Schlafli.zOpp = G.axis4 , G.axis5
pairAxes Schlafli.xNegYNeg = G.axis0 , G.axis2
pairAxes Schlafli.xNegYPos = G.axis0 , G.axis3
pairAxes Schlafli.xPosYNeg = G.axis1 , G.axis2
pairAxes Schlafli.xPosYPos = G.axis1 , G.axis3
pairAxes Schlafli.xNegZNeg = G.axis0 , G.axis4
pairAxes Schlafli.xNegZPos = G.axis0 , G.axis5
pairAxes Schlafli.xPosZNeg = G.axis1 , G.axis4
pairAxes Schlafli.xPosZPos = G.axis1 , G.axis5
pairAxes Schlafli.yNegZNeg = G.axis2 , G.axis4
pairAxes Schlafli.yNegZPos = G.axis2 , G.axis5
pairAxes Schlafli.yPosZNeg = G.axis3 , G.axis4
pairAxes Schlafli.yPosZPos = G.axis3 , G.axis5

middlePairCount : Nat
middlePairCount = 15

sixPlusFifteenPlusSix : Nat
sixPlusFifteenPlusSix = translationAxisCount + middlePairCount + modulationAxisCount

sixPlusFifteenPlusSixIs27 : sixPlusFifteenPlusSix ≡ 27
sixPlusFifteenPlusSixIs27 = refl

------------------------------------------------------------------------
-- 4. Same Schlaefli carrier, now typed by Heisenberg position/pair/dual roles.
------------------------------------------------------------------------

data HeisenbergSchlafli27 : Set where
  positionSix : G.Axis6 → HeisenbergSchlafli27
  bivectorFifteen : Schlafli.FacePair15 → HeisenbergSchlafli27
  dualSix : G.Axis6 → HeisenbergSchlafli27

schlafliToHeisenberg : Schlafli.Schlafli27Label → HeisenbergSchlafli27
schlafliToHeisenberg (Schlafli.leftFace face) = positionSix (faceToTranslationAxis face)
schlafliToHeisenberg (Schlafli.middlePair pair) = bivectorFifteen pair
schlafliToHeisenberg (Schlafli.rightFace face) = dualSix (faceToModulationAxis face)

heisenbergToSchlafli : HeisenbergSchlafli27 → Schlafli.Schlafli27Label
heisenbergToSchlafli (positionSix axis) = Schlafli.leftFace (translationAxisToFace axis)
heisenbergToSchlafli (bivectorFifteen pair) = Schlafli.middlePair pair
heisenbergToSchlafli (dualSix axis) = Schlafli.rightFace (modulationAxisToFace axis)

heisenbergAfterSchlafli :
  (label : Schlafli.Schlafli27Label) →
  heisenbergToSchlafli (schlafliToHeisenberg label) ≡ label
heisenbergAfterSchlafli (Schlafli.leftFace face) =
  cong Schlafli.leftFace (translationFaceRoundTrip face)
heisenbergAfterSchlafli (Schlafli.middlePair pair) = refl
heisenbergAfterSchlafli (Schlafli.rightFace face) =
  cong Schlafli.rightFace (modulationFaceRoundTrip face)

schlafliAfterHeisenberg :
  (label : HeisenbergSchlafli27) →
  schlafliToHeisenberg (heisenbergToSchlafli label) ≡ label
schlafliAfterHeisenberg (positionSix axis) =
  cong positionSix (translationAxisRoundTrip axis)
schlafliAfterHeisenberg (bivectorFifteen pair) = refl
schlafliAfterHeisenberg (dualSix axis) =
  cong dualSix (modulationAxisRoundTrip axis)

rawTernaryToHeisenberg27 : Geometry.Ternary27Point → HeisenbergSchlafli27
rawTernaryToHeisenberg27 point =
  schlafliToHeisenberg (Schlafli.pointToSchlafliLabel point)

heisenberg27ToRawTernary : HeisenbergSchlafli27 → Geometry.Ternary27Point
heisenberg27ToRawTernary label =
  Schlafli.schlafliLabelToPoint (heisenbergToSchlafli label)

rawAfterHeisenberg :
  (point : Geometry.Ternary27Point) →
  heisenberg27ToRawTernary (rawTernaryToHeisenberg27 point) ≡ point
rawAfterHeisenberg point
  rewrite heisenbergAfterSchlafli (Schlafli.pointToSchlafliLabel point) =
  Schlafli.pointAfterLabel point

heisenbergAfterRaw :
  (label : HeisenbergSchlafli27) →
  rawTernaryToHeisenberg27 (heisenberg27ToRawTernary label) ≡ label
heisenbergAfterRaw label
  rewrite Schlafli.labelAfterPoint (heisenbergToSchlafli label) =
  schlafliAfterHeisenberg label

------------------------------------------------------------------------
-- 5. Remaining action input is now one explicit normalizer-conjugation receipt.
--
-- It must say how an actor permutes the six translation generators, the six
-- modulation generators, and therefore the induced fifteen unordered pairs,
-- while respecting the Heisenberg commutator/symplectic pairing.  Once such a
-- receipt is supplied, the existing Schlaefli/minuscule action intertwiner can
-- consume it.  No source-native Monster normalizer action is invented here.
------------------------------------------------------------------------

record SixAxisNormalizerReceipt (Actor : Set) : Set₁ where
  field
    actTranslationAxis : Actor → G.Axis6 → G.Axis6
    actModulationAxis : Actor → G.Axis6 → G.Axis6

    translationGeneratorConjugationReceipt : Set
    modulationGeneratorConjugationReceipt : Set
    symplecticPairPreservedReceipt : Set
    inducedPair15ActionReceipt : Set
    inducedSchlafli27ActionReceipt : Set
    agreesWithA5FiveTranspositionsReceipt : Set
open SixAxisNormalizerReceipt public

record ThirteenSchlafliBoundary : Set where
  constructor thirteen-schlafli-boundary
  field
    extraspecialOnePlusSixPlusSixTyped : Bool
    centralPhaseKeptSeparateFrom27Vertices : Bool
    faceToTranslationSixTwoSided : Bool
    faceToModulationSixTwoSided : Bool
    fifteenPairsOnSameSixAxesTyped : Bool
    rawTernaryToHeisenbergSixFifteenSixTwoSided : Bool
    translationModulationSymplecticPairingConsumed : Bool
    actualNormalizerSixAxisConjugationPaidHere : Bool
    a5FiveTranspositionsSameActionPaidHere : Bool
    albertJordanProductPaidHere : Bool
    boundaryNote : String
open ThirteenSchlafliBoundary public

canonicalThirteenSchlafliBoundary : ThirteenSchlafliBoundary
canonicalThirteenSchlafliBoundary =
  thirteen-schlafli-boundary
    true true true true true true true
    false false false
    "The existing Ternary27Point is now two-sided with a Heisenberg-typed 6+15+6 carrier: left six = translation axes X, middle fifteen = unordered axis pairs / Lambda2 basis shape, right six = modulation/dual axes X*. The central C3 phase remains the +1 in 3^(1+12), not a Schlaefli vertex. Remaining action seam is exactly a source-native normalizer conjugation receipt on the six translation/modulation generators that agrees with the paid A5/S6 five-transposition action."
