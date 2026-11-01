module DASHI.Reasoning.Trialectic369CechGrothendieckComparisonExact where

------------------------------------------------------------------------
-- RELATIONAL GROTHENDIECK TRIANGLE <-> BASE369 CORNER CECH 1-SKELETON
--
-- DASHI CONTRIBUTION
--
-- The relational cover has three pairwise charts U_AB, U_BC, U_CA and
-- pairwise overlap objects A, B, C.
--
-- A selected corner of the Base369 27-cube has three incident faces X,Y,Z and
-- exactly three pairwise incident edges XY,YZ,XZ.
--
-- These two objects therefore share an exact *triangular Cech 1-skeleton*:
--
--   AB <-> X-face       AB∩BC = B <-> XY-edge
--   BC <-> Y-face       BC∩CA = C <-> YZ-edge
--   CA <-> Z-face       CA∩AB = A <-> XZ-edge
--
-- The Base369 boundary nerve additionally has a literal triple-overlap corner.
-- The current relational Grothendieck site does not expose a separate
-- triple-intersection site object.  Its irreducible triadic face/residual is a
-- different typed layer and is not silently identified with that corner.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27CornerEightExact as Corners
import DASHI.Foundations.Base369Ternary27BoundaryNerveExact as Nerve
import DASHI.Moonshine.Base369Ternary27FaceHypercubeAttachmentBidiExact as Face

------------------------------------------------------------------------
-- 1. Common abstract triangular cover shape.
------------------------------------------------------------------------

data TriadicPatch : Set where
  patchAB patchBC patchCA : TriadicPatch

data TriadicPairOverlap : Set where
  overlapA overlapB overlapC : TriadicPairOverlap

firstPatch : TriadicPairOverlap -> TriadicPatch
firstPatch overlapA = patchCA
firstPatch overlapB = patchAB
firstPatch overlapC = patchBC

secondPatch : TriadicPairOverlap -> TriadicPatch
secondPatch overlapA = patchAB
secondPatch overlapB = patchBC
secondPatch overlapC = patchCA

------------------------------------------------------------------------
-- 2. Exact relational-site realization of the triangle.
------------------------------------------------------------------------

relationalPatchObject : TriadicPatch -> Site.RelObj
relationalPatchObject patchAB = Site.edgeAB
relationalPatchObject patchBC = Site.edgeBC
relationalPatchObject patchCA = Site.edgeCA

relationalOverlapObject : TriadicPairOverlap -> Site.RelObj
relationalOverlapObject overlapA = Site.vertexA
relationalOverlapObject overlapB = Site.vertexB
relationalOverlapObject overlapC = Site.vertexC

relationalOverlapToFirst :
  (overlap : TriadicPairOverlap) ->
  Site.RelHom
    (relationalOverlapObject overlap)
    (relationalPatchObject (firstPatch overlap))
relationalOverlapToFirst overlapA = Site.aToCA
relationalOverlapToFirst overlapB = Site.bToAB
relationalOverlapToFirst overlapC = Site.cToBC

relationalOverlapToSecond :
  (overlap : TriadicPairOverlap) ->
  Site.RelHom
    (relationalOverlapObject overlap)
    (relationalPatchObject (secondPatch overlap))
relationalOverlapToSecond overlapA = Site.aToAB
relationalOverlapToSecond overlapB = Site.bToBC
relationalOverlapToSecond overlapC = Site.cToCA

------------------------------------------------------------------------
-- 3. Exact selected-corner Base369 realization of the same 1-skeleton.
------------------------------------------------------------------------

hypercubePatchFace :
  Corners.Corner3 ->
  TriadicPatch ->
  Geometry.Face6
hypercubePatchFace corner patchAB =
  Face.incidentXFace (Face.cornerIncidentFaces corner)
hypercubePatchFace corner patchBC =
  Face.incidentYFace (Face.cornerIncidentFaces corner)
hypercubePatchFace corner patchCA =
  Face.incidentZFace (Face.cornerIncidentFaces corner)

hypercubeOverlapEdge :
  Corners.Corner3 ->
  TriadicPairOverlap ->
  Nerve.Edge12
hypercubeOverlapEdge corner overlapA =
  Nerve.incidentXZEdge (Nerve.cornerIncidentEdges corner)
hypercubeOverlapEdge corner overlapB =
  Nerve.incidentXYEdge (Nerve.cornerIncidentEdges corner)
hypercubeOverlapEdge corner overlapC =
  Nerve.incidentYZEdge (Nerve.cornerIncidentEdges corner)

hypercubeOverlapFirstFace :
  (corner : Corners.Corner3) ->
  (overlap : TriadicPairOverlap) ->
  Nerve.edgeFirstFace (hypercubeOverlapEdge corner overlap)
  ≡ hypercubePatchFace corner (firstPatch overlap)
hypercubeOverlapFirstFace
  (Corners.corner3 x y z) overlapA = refl
hypercubeOverlapFirstFace
  (Corners.corner3 x y z) overlapB = refl
hypercubeOverlapFirstFace
  (Corners.corner3 x y z) overlapC = refl

hypercubeOverlapSecondFace :
  (corner : Corners.Corner3) ->
  (overlap : TriadicPairOverlap) ->
  Nerve.edgeSecondFace (hypercubeOverlapEdge corner overlap)
  ≡ hypercubePatchFace corner (secondPatch overlap)
hypercubeOverlapSecondFace
  (Corners.corner3 x y z) overlapA = refl
hypercubeOverlapSecondFace
  (Corners.corner3 x y z) overlapB = refl
hypercubeOverlapSecondFace
  (Corners.corner3 x y z) overlapC = refl

hypercubeCornerIsOnOverlap :
  (corner : Corners.Corner3) ->
  (overlap : TriadicPairOverlap) ->
  Nerve.OnEdge
    (hypercubeOverlapEdge corner overlap)
    (Corners.cornerPoint corner)
hypercubeCornerIsOnOverlap corner overlapA =
  Nerve.cornerOnIncidentXZEdge corner
hypercubeCornerIsOnOverlap corner overlapB =
  Nerve.cornerOnIncidentXYEdge corner
hypercubeCornerIsOnOverlap corner overlapC =
  Nerve.cornerOnIncidentYZEdge corner

------------------------------------------------------------------------
-- 4. Exact 1-skeleton comparison receipt.
------------------------------------------------------------------------

record TriadicCechOneSkeletonComparison
    (corner : Corners.Corner3) : Set where
  constructor triadic-cech-one-skeleton-comparison
  field
    relationalPatch :
      TriadicPatch -> Site.RelObj

    hypercubePatch :
      TriadicPatch -> Geometry.Face6

    relationalOverlap :
      TriadicPairOverlap -> Site.RelObj

    hypercubeOverlap :
      TriadicPairOverlap -> Nerve.Edge12

    hypercubeFirstIncidence :
      (overlap : TriadicPairOverlap) ->
      Nerve.edgeFirstFace (hypercubeOverlap overlap)
      ≡ hypercubePatch (firstPatch overlap)

    hypercubeSecondIncidence :
      (overlap : TriadicPairOverlap) ->
      Nerve.edgeSecondFace (hypercubeOverlap overlap)
      ≡ hypercubePatch (secondPatch overlap)

    relationalFirstIncidence :
      (overlap : TriadicPairOverlap) ->
      Site.RelHom
        (relationalOverlap overlap)
        (relationalPatch (firstPatch overlap))

    relationalSecondIncidence :
      (overlap : TriadicPairOverlap) ->
      Site.RelHom
        (relationalOverlap overlap)
        (relationalPatch (secondPatch overlap))

open TriadicCechOneSkeletonComparison public

canonicalTriadicCechOneSkeletonComparison :
  (corner : Corners.Corner3) ->
  TriadicCechOneSkeletonComparison corner
canonicalTriadicCechOneSkeletonComparison corner =
  triadic-cech-one-skeleton-comparison
    relationalPatchObject
    (hypercubePatchFace corner)
    relationalOverlapObject
    (hypercubeOverlapEdge corner)
    (hypercubeOverlapFirstFace corner)
    (hypercubeOverlapSecondFace corner)
    relationalOverlapToFirst
    relationalOverlapToSecond

------------------------------------------------------------------------
-- 5. Triple-overlap boundary.
------------------------------------------------------------------------

data RelationalTripleIntersectionSiteObjectCurrentlyExposed : Set where

noRelationalTripleIntersectionSiteObjectCurrentlyExposed :
  RelationalTripleIntersectionSiteObjectCurrentlyExposed -> ⊥
noRelationalTripleIntersectionSiteObjectCurrentlyExposed ()

hypercubeTripleOverlap :
  Corners.Corner3 ->
  Corners.Corner3
hypercubeTripleOverlap corner = corner

data TriadicFaceIsDefinitionallyHypercubeCorner : Set where
data OneSkeletonComparisonIsFullNerveEquivalence : Set where

triadicFaceIsNotDefinitionallyHypercubeCorner :
  TriadicFaceIsDefinitionallyHypercubeCorner -> ⊥
triadicFaceIsNotDefinitionallyHypercubeCorner ()

oneSkeletonComparisonDoesNotPromoteToFullNerveEquivalence :
  OneSkeletonComparisonIsFullNerveEquivalence -> ⊥
oneSkeletonComparisonDoesNotPromoteToFullNerveEquivalence ()

record Trialectic369CechGrothendieckComparisonBoundary : Set where
  constructor trialectic-369-cech-grothendieck-comparison-boundary
  field
    threePatchTriangleShared : Bool
    threePairwiseOverlapsShared : Bool
    incidencePreservedExactly : Bool
    selectedHypercubeCornerSuppliesTripleOverlap : Bool
    relationalSiteHasSeparateTripleIntersectionObject : Bool
    irreducibleTriadicFaceIdentifiedWithCorner : Bool
    oneSkeletonComparisonIsFullNerveEquivalence : Bool

canonicalTrialectic369CechGrothendieckComparisonBoundary :
  Trialectic369CechGrothendieckComparisonBoundary
canonicalTrialectic369CechGrothendieckComparisonBoundary =
  trialectic-369-cech-grothendieck-comparison-boundary
    true true true true false false false
