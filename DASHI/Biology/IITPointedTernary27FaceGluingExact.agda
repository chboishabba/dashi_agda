module DASHI.Biology.IITPointedTernary27FaceGluingExact where

------------------------------------------------------------------------
-- POINTED 27-CUBE / FACE-GLUING / IIT BRIDGE
--
-- A Base369 Ternary27Point is one point of {-1,0,+1}^3, hence one selected
-- cubie out of 27.  This file keeps four layers distinct:
--
--   (1) selection: one active point in the 27-carrier;
--   (2) geometry: whether that point lies on a particular outer face;
--   (3) gluing: invertible/equivariant edge transports + corner cocycle;
--   (4) IIT use: an observer may consume any of the above, but none is
--       definitionally identical to phi or phenomenal identity.
--
-- The canonical origin stratification gives the literal arithmetic
--   27 = 1 centre + 6 face-centres + 12 edge-centres + 8 corners = 1 + 26.
-- For an arbitrary selected cubie we retain the exact 27-carrier cardinality,
-- but do NOT pretend that the origin-centred 6/12/8 geometric strata are the
-- selected cubie's complement strata.  A translated/cyclic F3 chart is a
-- separate algebraic structure from the non-periodic cube geometry.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin.Base using (Fin)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Strata
import DASHI.Foundations.Base369Ternary27CornerEightExact as Corners
import DASHI.Foundations.Base369Ternary27BoundaryNerveExact as Nerve
import DASHI.Foundations.Base369FaceSheetPunctureIncidenceIdentityExact as FaceSheet
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Base369Ternary27FaceHypercubeCechGluingBidiExact as Cech
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Recognition
import DASHI.Moonshine.Base369Monster3BZetaFaceHypercubeGluingCompilerExact as ZetaGluing
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Trialectic
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

------------------------------------------------------------------------
-- 1. One selected/active cubie in the exact 27-state carrier.
------------------------------------------------------------------------

record PointedTernary27Cube : Set where
  constructor pointed-ternary27-cube
  field
    activeCubie : Geometry.Ternary27Point
open PointedTernary27Cube public

canonicalCentrePointedCube : PointedTernary27Cube
canonicalCentrePointedCube = pointed-ternary27-cube Geometry.origin

selectedCubieCount : Nat
selectedCubieCount = 1

remainingCubieCount : Nat
remainingCubieCount = 26

oneSelectedPlusTwentySixRemainingIsTwentySeven :
  selectedCubieCount + remainingCubieCount ≡ Geometry.hypervoxelStateCount
oneSelectedPlusTwentySixRemainingIsTwentySeven = refl

-- The existing origin-centred stratification identifies the 26 noncentral
-- cubies exactly as 6 + 12 + 8.
canonicalNoncentralCount : Nat
canonicalNoncentralCount =
  Strata.faceCentreCount + Strata.edgeCentreCount + Strata.cornerCount

canonicalNoncentralCountIsTwentySix :
  canonicalNoncentralCount ≡ 26
canonicalNoncentralCountIsTwentySix = refl

centrePlusBoundaryStrataIsTwentySeven :
  Strata.centreCount + canonicalNoncentralCount ≡ 27
centrePlusBoundaryStrataIsTwentySeven = refl

------------------------------------------------------------------------
-- 2. Face activity is proof-relevant: selection alone does not create a face.
------------------------------------------------------------------------

record ActiveFaceChart : Set where
  constructor active-face-chart
  field
    pointedCube : PointedTernary27Cube
    selectedFace : Geometry.Face6
    activeCubieOnSelectedFace :
      Geometry.OnFace selectedFace (activeCubie pointedCube)
    faceHypercubeState : H.X6
open ActiveFaceChart public

-- The central selected cubie has no outer-face witness.  Thus a pointed cube
-- is not automatically gluable through an outer face merely because it has an
-- active cubie.
originNotOnOuterFace :
  (face : Geometry.Face6) →
  Geometry.OnFace face Geometry.origin →
  ⊥
originNotOnOuterFace Geometry.xNegativeFace (Geometry.onFace ())
originNotOnOuterFace Geometry.xPositiveFace (Geometry.onFace ())
originNotOnOuterFace Geometry.yNegativeFace (Geometry.onFace ())
originNotOnOuterFace Geometry.yPositiveFace (Geometry.onFace ())
originNotOnOuterFace Geometry.zNegativeFace (Geometry.onFace ())
originNotOnOuterFace Geometry.zPositiveFace (Geometry.onFace ())

------------------------------------------------------------------------
-- 3. Each outer face is itself a pointed-compatible 9-sheet: 9 = 1 + 8.
------------------------------------------------------------------------

outerFaceSheetCount : Nat
outerFaceSheetCount = FaceSheet.faceSheetCount

outerFacePunctureCount : Nat
outerFacePunctureCount = FaceSheet.puncturedFaceCount

outerFaceSheetIsOnePlusEight :
  1 + outerFacePunctureCount ≡ outerFaceSheetCount
outerFaceSheetIsOnePlusEight = FaceSheet.faceSheetIsOnePlusEight

------------------------------------------------------------------------
-- 4. Pairwise active-face gluing is constrained by the existing Cech owner.
--
-- It is not enough that two active cubies each lie on some face.  Their chosen
-- face charts must be the two faces of one boundary-nerve edge and their X6
-- states must agree after the certified oriented edge transport.
------------------------------------------------------------------------

record PairwiseActiveFaceGluing
    {Actor : Set}
    (gluing : Cech.FaceHypercubeCechGluing Actor)
    (left right : ActiveFaceChart) : Set where
  constructor pairwise-active-face-gluing
  field
    overlapEdge : Nerve.Edge12
    leftFaceMatchesEdge :
      selectedFace left ≡ Nerve.edgeFirstFace overlapEdge
    rightFaceMatchesEdge :
      selectedFace right ≡ Nerve.edgeSecondFace overlapEdge
    transportedActiveStateMatches :
      Cech.edgeTransport gluing overlapEdge (faceHypercubeState left)
      ≡ faceHypercubeState right
open PairwiseActiveFaceGluing public

------------------------------------------------------------------------
-- 5. Triple compatibility is stronger than three unconstrained pairwise links.
--
-- At a literal cube corner the three pairwise overlaps are xy, xz and yz.
-- The existing Cech owner requires the triple-overlap cocycle
--
--     T_xz = T_yz o T_xy.
--
-- This is the precise finite compatibility law that rules out arbitrary face
-- gluing around a selected corner.
------------------------------------------------------------------------

selectedCornerCocycle :
  {Actor : Set} →
  (gluing : Cech.FaceHypercubeCechGluing Actor) →
  (corner : Corners.Corner3) →
  (state : H.X6) →
  let edges = Nerve.cornerIncidentEdges corner
  in Cech.edgeTransport gluing (Nerve.incidentXZEdge edges) state
   ≡ Cech.edgeTransport gluing (Nerve.incidentYZEdge edges)
       (Cech.edgeTransport gluing (Nerve.incidentXYEdge edges) state)
selectedCornerCocycle gluing = Cech.cornerCocycle gluing

------------------------------------------------------------------------
-- 6. Three pointed cubes are exactly the active-coordinate view of the mature
--    three-cube hyperfabric carrier.
------------------------------------------------------------------------

record PointedThreeCubeHyperform : Set where
  constructor pointed-three-cube-hyperform
  field
    interactionCube : PointedTernary27Cube
    appraisalACube : PointedTernary27Cube
    appraisalBCube : PointedTernary27Cube
open PointedThreeCubeHyperform public

pointedThreeToHyperform :
  PointedThreeCubeHyperform → Geometry.TernaryHyperformalPoint
pointedThreeToHyperform pointed =
  Geometry.ternaryHyperformalPoint
    (activeCubie (interactionCube pointed))
    (activeCubie (appraisalACube pointed))
    (activeCubie (appraisalBCube pointed))

hyperformToPointedThree :
  Geometry.TernaryHyperformalPoint → PointedThreeCubeHyperform
hyperformToPointedThree fabric =
  pointed-three-cube-hyperform
    (pointed-ternary27-cube (Geometry.interactionVoxel fabric))
    (pointed-ternary27-cube (Geometry.appraisalAVoxel fabric))
    (pointed-ternary27-cube (Geometry.appraisalBVoxel fabric))

pointedThreeHyperformRoundTrip :
  (pointed : PointedThreeCubeHyperform) →
  hyperformToPointedThree (pointedThreeToHyperform pointed) ≡ pointed
pointedThreeHyperformRoundTrip
  (pointed-three-cube-hyperform
    (pointed-ternary27-cube i)
    (pointed-ternary27-cube a)
    (pointed-ternary27-cube b)) = refl

hyperformPointedThreeRoundTrip :
  (fabric : Geometry.TernaryHyperformalPoint) →
  pointedThreeToHyperform (hyperformToPointedThree fabric) ≡ fabric
hyperformPointedThreeRoundTrip
  (Geometry.ternaryHyperformalPoint i a b) = refl

threeActiveCubieChoiceCount : Nat
threeActiveCubieChoiceCount = 27 * 27 * 27

threeActiveCubieChoiceCountIsHyperformCount :
  threeActiveCubieChoiceCount ≡ Geometry.hyperfabricStateCount
threeActiveCubieChoiceCountIsHyperformCount = refl

------------------------------------------------------------------------
-- 7. Cyclotomic / Monster-3B zeta recognition provides a concrete actual
--    face-gluing promotion when its source recognition is supplied.
--
-- This is deliberately conditional on ActualZetaSectorRecognition.  The IIT
-- bridge consumes the existing theorem; it does not manufacture recognition.
------------------------------------------------------------------------

recognizedZetaFaceGluing :
  ∀ {ActualSector : Set} →
  (recognition : Recognition.ActualZetaSectorRecognition ActualSector) →
  Fin 90 →
  Cech.ActualFaceHypercubeGluingPromotion H.Axis6 ActualSector
recognizedZetaFaceGluing = ZetaGluing.zetaFaceHypercubeGluing

------------------------------------------------------------------------
-- 8. Pairwise/structured boundary information still need not determine the
--    irreducible triadic face.  Reuse the existing exact non-descent theorem.
------------------------------------------------------------------------

pairwiseStructuredBoundaryDoesNotDetermineTriadicFace :
  Descent.FactorsThrough
    Trialectic.structuredBoundaryObserver
    Trialectic.structuredFaceConsumer
  → ⊥
pairwiseStructuredBoundaryDoesNotDetermineTriadicFace =
  Trialectic.structuredThreeCellBoundaryDoesNotDetermineFace

------------------------------------------------------------------------
-- 9. Promotion boundary for IIT.
------------------------------------------------------------------------

record IITPointedTernary27Boundary : Set where
  constructor iit-pointed-ternary27-boundary
  field
    carrierIsThreeCubed : Bool
    oneSelectedPlusTwentySixCardinalityOwned : Bool
    originCentredTwentySixStratifiedAsSixTwelveEight : Bool
    everyOuterFaceIsNineEqualsOnePlusEight : Bool
    activeCubieSelectionAutomaticallyCreatesFaceWitness : Bool
    pairwiseFaceGluingRequiresCertifiedEdgeTransport : Bool
    tripleCornerGluingRequiresCocycle : Bool
    threePointedCubesRechartToExistingHyperform : Bool
    zetaRecognitionCanCompileActualFaceGluing : Bool
    zetaRecognitionConstructedByThisBridge : Bool
    pairwiseStructuredBoundaryDeterminesTriadicFace : Bool
    arbitrarySelectedCubieComplementStratifiedLikeOriginByDefinition : Bool
    compatibleFaceGluingEqualsIITPhiByDefinition : Bool

open IITPointedTernary27Boundary public

canonicalIITPointedTernary27Boundary : IITPointedTernary27Boundary
canonicalIITPointedTernary27Boundary =
  iit-pointed-ternary27-boundary
    true true true true
    false true true true true
    false false false false

selectionDoesNotCreateFaceWitness :
  activeCubieSelectionAutomaticallyCreatesFaceWitness
    canonicalIITPointedTernary27Boundary ≡ false
selectionDoesNotCreateFaceWitness = refl

pairwiseBoundaryDoesNotForceTriadicFace :
  pairwiseStructuredBoundaryDeterminesTriadicFace
    canonicalIITPointedTernary27Boundary ≡ false
pairwiseBoundaryDoesNotForceTriadicFace = refl

faceGluingDoesNotSelfPromoteToPhi :
  compatibleFaceGluingEqualsIITPhiByDefinition
    canonicalIITPointedTernary27Boundary ≡ false
faceGluingDoesNotSelfPromoteToPhi = refl
