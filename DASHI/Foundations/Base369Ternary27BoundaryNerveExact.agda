module DASHI.Foundations.Base369Ternary27BoundaryNerveExact where

------------------------------------------------------------------------
-- EXACT BOUNDARY NERVE OF THE BASE369 TERNARY 27-CUBE
--
-- The existing geometry owns six literal outer faces and eight literal
-- corners.  This owner inserts the missing middle stratum: the twelve
-- intersections of non-opposite face pairs.  The resulting incidence nerve is
--
--   6 faces  <-  12 edges  <-  8 corners.
--
-- An edge is one choice of signs on one of the axis pairs xy, xz, yz.  Every
-- corner selects exactly one edge of each pair type.  All incidence proofs are
-- against the existing Geometry.OnFace relation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27CornerEightExact as Corners
import DASHI.Moonshine.Base369Ternary27FaceHypercubeAttachmentBidiExact as Face

------------------------------------------------------------------------
-- 1. Twelve literal edges = 3 axis pairs x 2 signs x 2 signs.
------------------------------------------------------------------------

data Edge12 : Set where
  edgeXY : Corners.OuterSign → Corners.OuterSign → Edge12
  edgeXZ : Corners.OuterSign → Corners.OuterSign → Edge12
  edgeYZ : Corners.OuterSign → Corners.OuterSign → Edge12

edgeFirstFace : Edge12 → Geometry.Face6
edgeFirstFace (edgeXY x y) = Face.xIncidentFace x
edgeFirstFace (edgeXZ x z) = Face.xIncidentFace x
edgeFirstFace (edgeYZ y z) = Face.yIncidentFace y

edgeSecondFace : Edge12 → Geometry.Face6
edgeSecondFace (edgeXY x y) = Face.yIncidentFace y
edgeSecondFace (edgeXZ x z) = Face.zIncidentFace z
edgeSecondFace (edgeYZ y z) = Face.zIncidentFace z

-- A canonical midpoint witness on every geometric edge.
edgeMidpoint : Edge12 → Geometry.Ternary27Point
edgeMidpoint (edgeXY x y) =
  Geometry.ternary27Point (Corners.outerTrit x) (Corners.outerTrit y) SSP.sspZero
edgeMidpoint (edgeXZ x z) =
  Geometry.ternary27Point (Corners.outerTrit x) SSP.sspZero (Corners.outerTrit z)
edgeMidpoint (edgeYZ y z) =
  Geometry.ternary27Point SSP.sspZero (Corners.outerTrit y) (Corners.outerTrit z)

record OnEdge (edge : Edge12) (point : Geometry.Ternary27Point) : Set where
  constructor onEdge
  field
    onFirstFace : Geometry.OnFace (edgeFirstFace edge) point
    onSecondFace : Geometry.OnFace (edgeSecondFace edge) point
open OnEdge public

edgeMidpointOnEdge : (edge : Edge12) → OnEdge edge (edgeMidpoint edge)
edgeMidpointOnEdge (edgeXY Corners.negativeOuter Corners.negativeOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
edgeMidpointOnEdge (edgeXY Corners.negativeOuter Corners.positiveOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
edgeMidpointOnEdge (edgeXY Corners.positiveOuter Corners.negativeOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
edgeMidpointOnEdge (edgeXY Corners.positiveOuter Corners.positiveOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
edgeMidpointOnEdge (edgeXZ Corners.negativeOuter Corners.negativeOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
edgeMidpointOnEdge (edgeXZ Corners.negativeOuter Corners.positiveOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
edgeMidpointOnEdge (edgeXZ Corners.positiveOuter Corners.negativeOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
edgeMidpointOnEdge (edgeXZ Corners.positiveOuter Corners.positiveOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
edgeMidpointOnEdge (edgeYZ Corners.negativeOuter Corners.negativeOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
edgeMidpointOnEdge (edgeYZ Corners.negativeOuter Corners.positiveOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
edgeMidpointOnEdge (edgeYZ Corners.positiveOuter Corners.negativeOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
edgeMidpointOnEdge (edgeYZ Corners.positiveOuter Corners.positiveOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)

------------------------------------------------------------------------
-- 2. Every corner selects exactly three edges: xy, xz and yz.
------------------------------------------------------------------------

record CornerIncidentEdgeTriple : Set where
  constructor cornerIncidentEdgeTriple
  field
    incidentXYEdge : Edge12
    incidentXZEdge : Edge12
    incidentYZEdge : Edge12
open CornerIncidentEdgeTriple public

cornerIncidentEdges : Corners.Corner3 → CornerIncidentEdgeTriple
cornerIncidentEdges (Corners.corner3 x y z) =
  cornerIncidentEdgeTriple (edgeXY x y) (edgeXZ x z) (edgeYZ y z)

cornerOnIncidentXYEdge :
  (corner : Corners.Corner3) →
  OnEdge (incidentXYEdge (cornerIncidentEdges corner)) (Corners.cornerPoint corner)
cornerOnIncidentXYEdge (Corners.corner3 Corners.negativeOuter Corners.negativeOuter z) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
cornerOnIncidentXYEdge (Corners.corner3 Corners.negativeOuter Corners.positiveOuter z) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
cornerOnIncidentXYEdge (Corners.corner3 Corners.positiveOuter Corners.negativeOuter z) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
cornerOnIncidentXYEdge (Corners.corner3 Corners.positiveOuter Corners.positiveOuter z) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)

cornerOnIncidentXZEdge :
  (corner : Corners.Corner3) →
  OnEdge (incidentXZEdge (cornerIncidentEdges corner)) (Corners.cornerPoint corner)
cornerOnIncidentXZEdge (Corners.corner3 Corners.negativeOuter y Corners.negativeOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
cornerOnIncidentXZEdge (Corners.corner3 Corners.negativeOuter y Corners.positiveOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
cornerOnIncidentXZEdge (Corners.corner3 Corners.positiveOuter y Corners.negativeOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
cornerOnIncidentXZEdge (Corners.corner3 Corners.positiveOuter y Corners.positiveOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)

cornerOnIncidentYZEdge :
  (corner : Corners.Corner3) →
  OnEdge (incidentYZEdge (cornerIncidentEdges corner)) (Corners.cornerPoint corner)
cornerOnIncidentYZEdge (Corners.corner3 x Corners.negativeOuter Corners.negativeOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
cornerOnIncidentYZEdge (Corners.corner3 x Corners.negativeOuter Corners.positiveOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
cornerOnIncidentYZEdge (Corners.corner3 x Corners.positiveOuter Corners.negativeOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)
cornerOnIncidentYZEdge (Corners.corner3 x Corners.positiveOuter Corners.positiveOuter) =
  onEdge (Geometry.onFace refl) (Geometry.onFace refl)

------------------------------------------------------------------------
-- 3. Typed incidence ledger.
------------------------------------------------------------------------

faceCount : Nat
faceCount = 6

edgeCount : Nat
edgeCount = 12

cornerCount : Nat
cornerCount = 8

record BoundaryNerveBoundary : Set where
  constructor boundaryNerveBoundary
  field
    sixFacesOwned : Bool
    twelveEdgeCarrierConstructed : Bool
    everyEdgeHasTwoExistingFaceWitnesses : Bool
    eightCornerCarrierOwned : Bool
    everyCornerSelectsThreeEdges : Bool
    cornerEdgeIncidenceUsesExistingOnFaceGeometry : Bool
    boundaryNerveAloneConstructsFibreGluing : Bool
    boundaryNerveAloneConstructsMonsterAction : Bool

canonicalBoundaryNerveBoundary : BoundaryNerveBoundary
canonicalBoundaryNerveBoundary =
  boundaryNerveBoundary true true true true true true false false
