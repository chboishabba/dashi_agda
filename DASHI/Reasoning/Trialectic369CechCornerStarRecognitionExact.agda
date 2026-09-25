module DASHI.Reasoning.Trialectic369CechCornerStarRecognitionExact where

------------------------------------------------------------------------
-- RELATIONAL AB/BC/CA COVER -> SELECTED X6 CECH CORNER STAR
--
-- DASHI CONTRIBUTION
--
-- The relational cover has three local charts:
--
--   U_AB, U_BC, U_CA
--
-- with pairwise overlaps A, B, C.  The existing ternary-cube Cech nerve has,
-- at every corner, exactly three incident faces and the three pairwise edges
-- between them.
--
-- Choosing one corner therefore gives an exact incidence embedding:
--
--   U_AB -> X-face
--   U_BC -> Y-face
--   U_CA -> Z-face
--
--   B = U_AB ∩ U_BC -> XY edge
--   A = U_AB ∩ U_CA -> XZ edge
--   C = U_BC ∩ U_CA -> YZ edge.
--
-- This pays the local-cover incidence comparison.  It does NOT identify the
-- relational Grothendieck site with the full 6-face/12-edge/8-corner nerve,
-- nor does it construct the X6 actual-state gluing promotion.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27CornerEightExact as Corners
import DASHI.Foundations.Base369Ternary27BoundaryNerveExact as Nerve
import DASHI.Moonshine.Base369Ternary27FaceHypercubeCechGluingBidiExact as Cech
import DASHI.Reasoning.Trialectic369DescentNaturalityExact as Descent

------------------------------------------------------------------------
-- 1. Typed source chart/overlap roles.
------------------------------------------------------------------------

data RelationalLocalChart3 : Set where
  localAB : RelationalLocalChart3
  localBC : RelationalLocalChart3
  localCA : RelationalLocalChart3

data RelationalOverlap3 : Set where
  overlapA : RelationalOverlap3
  overlapB : RelationalOverlap3
  overlapC : RelationalOverlap3

localChartObject : RelationalLocalChart3 -> Site.RelObj
localChartObject localAB = Site.edgeAB
localChartObject localBC = Site.edgeBC
localChartObject localCA = Site.edgeCA

overlapObject : RelationalOverlap3 -> Site.RelObj
overlapObject overlapA = Site.vertexA
overlapObject overlapB = Site.vertexB
overlapObject overlapC = Site.vertexC

------------------------------------------------------------------------
-- 2. Select one literal X6 corner star.
------------------------------------------------------------------------

selectedCorner : Corners.Corner3
selectedCorner =
  Corners.corner3
    Corners.negativeOuter
    Corners.negativeOuter
    Corners.negativeOuter

localChartFace : RelationalLocalChart3 -> Geometry.Face6
localChartFace localAB = Geometry.xNegativeFace
localChartFace localBC = Geometry.yNegativeFace
localChartFace localCA = Geometry.zNegativeFace

overlapEdge : RelationalOverlap3 -> Nerve.Edge12
overlapEdge overlapA =
  Nerve.edgeXZ Corners.negativeOuter Corners.negativeOuter
overlapEdge overlapB =
  Nerve.edgeXY Corners.negativeOuter Corners.negativeOuter
overlapEdge overlapC =
  Nerve.edgeYZ Corners.negativeOuter Corners.negativeOuter

------------------------------------------------------------------------
-- 3. Exact incidence preservation.
------------------------------------------------------------------------

overlapBFirstFaceIsAB :
  Nerve.edgeFirstFace (overlapEdge overlapB)
  ≡ localChartFace localAB
overlapBFirstFaceIsAB = refl

overlapBSecondFaceIsBC :
  Nerve.edgeSecondFace (overlapEdge overlapB)
  ≡ localChartFace localBC
overlapBSecondFaceIsBC = refl

overlapAFirstFaceIsAB :
  Nerve.edgeFirstFace (overlapEdge overlapA)
  ≡ localChartFace localAB
overlapAFirstFaceIsAB = refl

overlapASecondFaceIsCA :
  Nerve.edgeSecondFace (overlapEdge overlapA)
  ≡ localChartFace localCA
overlapASecondFaceIsCA = refl

overlapCFirstFaceIsBC :
  Nerve.edgeFirstFace (overlapEdge overlapC)
  ≡ localChartFace localBC
overlapCFirstFaceIsBC = refl

overlapCSecondFaceIsCA :
  Nerve.edgeSecondFace (overlapEdge overlapC)
  ≡ localChartFace localCA
overlapCSecondFaceIsCA = refl

selectedCornerXYIsOverlapB :
  Nerve.incidentXYEdge (Nerve.cornerIncidentEdges selectedCorner)
  ≡ overlapEdge overlapB
selectedCornerXYIsOverlapB = refl

selectedCornerXZIsOverlapA :
  Nerve.incidentXZEdge (Nerve.cornerIncidentEdges selectedCorner)
  ≡ overlapEdge overlapA
selectedCornerXZIsOverlapA = refl

selectedCornerYZIsOverlapC :
  Nerve.incidentYZEdge (Nerve.cornerIncidentEdges selectedCorner)
  ≡ overlapEdge overlapC
selectedCornerYZIsOverlapC = refl

------------------------------------------------------------------------
-- 4. Source Grothendieck cover and target Cech interface both remain owned.
------------------------------------------------------------------------

sourceCoverReceipt :
  Site.RelCover Site.triadicRelationalSieve
sourceCoverReceipt = Site.triadicRelationalSieveCovers

targetCechBoundary :
  Cech.FaceHypercubeCechBoundary
targetCechBoundary = Cech.canonicalFaceHypercubeCechBoundary

sourceDescentBoundary :
  Descent.Trialectic369DescentNaturalityBoundary
sourceDescentBoundary = Descent.canonicalTrialectic369DescentNaturalityBoundary

------------------------------------------------------------------------
-- 5. What this comparison does and does not establish.
--
-- The selected corner itself is a genuine triple-overlap stratum in the X6
-- nerve.  The relational site currently has globalABC plus three dyads plus
-- three pair-overlap vertices; it does not contain a separately typed
-- "triple-overlap corner" object.  Hence the comparison is an incidence
-- embedding into a corner star, not an equivalence of indexing categories.
------------------------------------------------------------------------

data RelationalCoverEqualsFullX6BoundaryNerve : Set where
data IncidenceEmbeddingAutomaticallyConstructsActualStatePromotion : Set where
data GlobalABCIsSelectedTripleOverlapCorner : Set where

relationalCoverDoesNotEqualFullX6BoundaryNerve :
  RelationalCoverEqualsFullX6BoundaryNerve -> ⊥
relationalCoverDoesNotEqualFullX6BoundaryNerve ()

incidenceEmbeddingDoesNotConstructActualStatePromotion :
  IncidenceEmbeddingAutomaticallyConstructsActualStatePromotion -> ⊥
incidenceEmbeddingDoesNotConstructActualStatePromotion ()

globalABCDoesNotAutomaticallyBecomeTripleOverlapCorner :
  GlobalABCIsSelectedTripleOverlapCorner -> ⊥
globalABCDoesNotAutomaticallyBecomeTripleOverlapCorner ()

------------------------------------------------------------------------
-- 6. Recognition contract for the remaining same-object promotion.
--
-- Once an Actor and one literal ActualState are supplied, the missing theorem
-- is exactly a Cech ActualFaceHypercubeGluingPromotion whose three selected
-- face charts agree with the declared AB/BC/CA chart embeddings.
------------------------------------------------------------------------

record CornerStarActualStateRecognition (Actor ActualState : Set) : Set₁ where
  field
    actualPromotion :
      Cech.ActualFaceHypercubeGluingPromotion Actor ActualState

    selectedABFaceIsXNegative :
      localChartFace localAB ≡ Geometry.xNegativeFace

    selectedBCFaceIsYNegative :
      localChartFace localBC ≡ Geometry.yNegativeFace

    selectedCAFaceIsZNegative :
      localChartFace localCA ≡ Geometry.zNegativeFace

open CornerStarActualStateRecognition public

record Trialectic369CechCornerStarRecognitionBoundary : Set where
  constructor trialectic-369-cech-corner-star-recognition-boundary
  field
    relationalThreeChartCoverOwned : Bool
    selectedThreeFaceCornerStarOwned : Bool
    threePairwiseOverlapEdgesMatchedExactly : Bool
    cornerIncidentEdgeTripleMatchedExactly : Bool
    incidenceComparisonPaid : Bool
    fullNerveEquivalencePaid : Bool
    actualSameObjectPromotionPaid : Bool
    remainingPromotionHasTypedContract : Bool

canonicalTrialectic369CechCornerStarRecognitionBoundary :
  Trialectic369CechCornerStarRecognitionBoundary
canonicalTrialectic369CechCornerStarRecognitionBoundary =
  trialectic-369-cech-corner-star-recognition-boundary
    true true true true true
    false false true
