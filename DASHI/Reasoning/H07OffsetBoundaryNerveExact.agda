module DASHI.Reasoning.H07OffsetBoundaryNerveExact where

-- Literal ternary offset fibre of a selected marked affine direction.
-- Reuse original SSP BIDI and 6/12/8 spatial nerve. Not H05 diagram faces,
-- nor the distinct X6 actor action of the Monster Cech interface.
open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; zer)
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as V
import DASHI.Foundations.Base369Ternary27BoundaryNerveExact as N
import DASHI.Foundations.Base369Ternary27CornerEightExact as K
import DASHI.Codec.TriadicMaskSignFactorization as M
import DASHI.Codec.IndexedCubeMaskSignExact as C
import DASHI.Reasoning.H07AtlasCodecConsumerExact as O
import DASHI.Reasoning.H07FullAtlasSectionExact as H
import DASHI.Reasoning.H07AtlasProjectionLawsExact as P
import DASHI.Reasoning.H07IntegerWindingExact as W
import DASHI.Reasoning.TypedHyperfabricCore as F

toPoint : M.Triple Trit → V.Ternary27Point
toPoint (M.triple a b c) =
  V.ternary27Point (SSP.fromTrit a) (SSP.fromTrit b) (SSP.fromTrit c)

fromPoint : V.Ternary27Point → M.Triple Trit
fromPoint (V.ternary27Point a b c) =
  M.triple (SSP.toTrit a) (SSP.toTrit b) (SSP.toTrit c)

reopen : (t : M.Triple Trit) → fromPoint (toPoint t) ≡ t
reopen (M.triple a b c)
  rewrite SSP.toTrit-fromTrit a | SSP.toTrit-fromTrit b
        | SSP.toTrit-fromTrit c = refl

reclose : (p : V.Ternary27Point) → toPoint (fromPoint p) ≡ p
reclose (V.ternary27Point a b c)
  rewrite SSP.fromTrit-toTrit a | SSP.fromTrit-toTrit b
        | SSP.fromTrit-toTrit c = refl

rotatePoint : V.Ternary27Point → V.Ternary27Point
rotatePoint (V.ternary27Point a b c) = V.ternary27Point b c a

rotateOffset : (x : M.Triple Trit) →
  toPoint (C.rotateTriple x) ≡ rotatePoint (toPoint x)
rotateOffset (M.triple a b c) = refl

rotateFace : V.Face6 → V.Face6
rotateFace V.xNegativeFace = V.zNegativeFace
rotateFace V.xPositiveFace = V.zPositiveFace
rotateFace V.yNegativeFace = V.xNegativeFace
rotateFace V.yPositiveFace = V.xPositiveFace
rotateFace V.zNegativeFace = V.yNegativeFace
rotateFace V.zPositiveFace = V.yPositiveFace

rotateOnFace : {f : V.Face6} {p : V.Ternary27Point} →
  V.OnFace f p → V.OnFace (rotateFace f) (rotatePoint p)
rotateOnFace {V.xNegativeFace} {V.ternary27Point a b c} (V.onFace e) = V.onFace e
rotateOnFace {V.xPositiveFace} {V.ternary27Point a b c} (V.onFace e) = V.onFace e
rotateOnFace {V.yNegativeFace} {V.ternary27Point a b c} (V.onFace e) = V.onFace e
rotateOnFace {V.yPositiveFace} {V.ternary27Point a b c} (V.onFace e) = V.onFace e
rotateOnFace {V.zNegativeFace} {V.ternary27Point a b c} (V.onFace e) = V.onFace e
rotateOnFace {V.zPositiveFace} {V.ternary27Point a b c} (V.onFace e) = V.onFace e

rotateEdge : N.Edge12 → N.Edge12
rotateEdge (N.edgeXY x y) = N.edgeXZ y x
rotateEdge (N.edgeXZ x z) = N.edgeYZ z x
rotateEdge (N.edgeYZ y z) = N.edgeXY y z

-- Source first/second face order reverses for XY and XZ.
rotateOnEdge : {e : N.Edge12} {p : V.Ternary27Point} →
  N.OnEdge e p → N.OnEdge (rotateEdge e) (rotatePoint p)
rotateOnEdge {N.edgeXY K.negativeOuter K.negativeOuter} (N.onEdge f g) =
  N.onEdge (rotateOnFace g) (rotateOnFace f)
rotateOnEdge {N.edgeXY K.negativeOuter K.positiveOuter} (N.onEdge f g) =
  N.onEdge (rotateOnFace g) (rotateOnFace f)
rotateOnEdge {N.edgeXY K.positiveOuter K.negativeOuter} (N.onEdge f g) =
  N.onEdge (rotateOnFace g) (rotateOnFace f)
rotateOnEdge {N.edgeXY K.positiveOuter K.positiveOuter} (N.onEdge f g) =
  N.onEdge (rotateOnFace g) (rotateOnFace f)
rotateOnEdge {N.edgeXZ K.negativeOuter K.negativeOuter} (N.onEdge f g) =
  N.onEdge (rotateOnFace g) (rotateOnFace f)
rotateOnEdge {N.edgeXZ K.negativeOuter K.positiveOuter} (N.onEdge f g) =
  N.onEdge (rotateOnFace g) (rotateOnFace f)
rotateOnEdge {N.edgeXZ K.positiveOuter K.negativeOuter} (N.onEdge f g) =
  N.onEdge (rotateOnFace g) (rotateOnFace f)
rotateOnEdge {N.edgeXZ K.positiveOuter K.positiveOuter} (N.onEdge f g) =
  N.onEdge (rotateOnFace g) (rotateOnFace f)
rotateOnEdge {N.edgeYZ K.negativeOuter K.negativeOuter} (N.onEdge f g) =
  N.onEdge (rotateOnFace f) (rotateOnFace g)
rotateOnEdge {N.edgeYZ K.negativeOuter K.positiveOuter} (N.onEdge f g) =
  N.onEdge (rotateOnFace f) (rotateOnFace g)
rotateOnEdge {N.edgeYZ K.positiveOuter K.negativeOuter} (N.onEdge f g) =
  N.onEdge (rotateOnFace f) (rotateOnFace g)
rotateOnEdge {N.edgeYZ K.positiveOuter K.positiveOuter} (N.onEdge f g) =
  N.onEdge (rotateOnFace f) (rotateOnFace g)

rotateCorner : K.Corner3 → K.Corner3
rotateCorner (K.corner3 a b c) = K.corner3 b c a

rotateCornerPoint : (c : K.Corner3) →
  K.cornerPoint (rotateCorner c) ≡ rotatePoint (K.cornerPoint c)
rotateCornerPoint (K.corner3 a b c) = refl

-- The centre remains in the global offset fibre; no outer face contains it.
centre : V.Ternary27Point
centre = V.ternary27Point SSP.sspZero SSP.sspZero SSP.sspZero

centreNotOnFace : (f : V.Face6) → V.OnFace f centre → ⊥
centreNotOnFace V.xNegativeFace (V.onFace ())
centreNotOnFace V.xPositiveFace (V.onFace ())
centreNotOnFace V.yNegativeFace (V.onFace ())
centreNotOnFace V.yPositiveFace (V.onFace ())
centreNotOnFace V.zNegativeFace (V.onFace ())
centreNotOnFace V.zPositiveFace (V.onFace ())

-- Selected actual offset fibre: slopes and anchor fixed; all 27 offsets
-- vary. Each spatial face has a supplied ADMISSIBLE affine chart, not
-- an asserted identification of six faces with six of ten pivot marks.
module At (p : H.Pivot) (u v : M.Triple Trit)
  (w : W.GovernedWindingContext) where

  zeroBlocks : C.Blocks Trit
  zeroBlocks = C.blocks u v (M.triple zer zer zer)

  L : H.Direction
  L = O.directionOf p zeroBlocks

  anchor : H.Mark L
  anchor = O.anchorOf p zeroBlocks

  offset : V.Ternary27Point → H.Vec5
  offset pt = O.offsetOf p (C.blocks u v (fromPoint pt))

  section : V.Ternary27Point → F.GlobalSection (H.fabric anchor)
  section pt = W.sectionFromWinding anchor (offset pt) w

  module Charts (faceMark : V.Face6 → H.Mark L) (q : H.Mark L) where

    localValue : (f : V.Face6) (pt : V.Ternary27Point) →
      V.OnFace f pt → H.Local anchor (faceMark f)
    localValue f pt member = F.vertexValue (section pt) (faceMark f)

    restriction : (f : V.Face6) (pt : V.Ternary27Point) →
      V.OnFace f pt → H.Shared anchor q
    restriction f pt member =
      H.restrict {p = anchor} {v = faceMark f} {q = q}
        H.sameDirection (localValue f pt member)

    matchesGlobal : (f : V.Face6) (pt : V.Ternary27Point) (member : V.OnFace f pt) →
      restriction f pt member ≡ F.edgeValue (section pt) q
    matchesGlobal f pt member =
      F.compatible (section pt) {vertex = faceMark f} {edge = q} H.sameDirection

    edgeAgreement : (e : N.Edge12) (pt : V.Ternary27Point) (m : N.OnEdge e pt) →
      restriction (N.edgeFirstFace e) pt (N.onFirstFace m)
        ≡ restriction (N.edgeSecondFace e) pt (N.onSecondFace m)
    edgeAgreement e pt m = trans
      (matchesGlobal (N.edgeFirstFace e) pt (N.onFirstFace m))
      (sym (matchesGlobal (N.edgeSecondFace e) pt (N.onSecondFace m)))

    -- The literal original three incident edges at every corner.
    cornerXY : (c : K.Corner3) →
      restriction (N.edgeFirstFace (N.incidentXYEdge (N.cornerIncidentEdges c))) (K.cornerPoint c)
        (N.onFirstFace (N.cornerOnIncidentXYEdge c))
      ≡ restriction (N.edgeSecondFace (N.incidentXYEdge (N.cornerIncidentEdges c))) (K.cornerPoint c)
        (N.onSecondFace (N.cornerOnIncidentXYEdge c))
    cornerXY c = edgeAgreement (N.incidentXYEdge (N.cornerIncidentEdges c))
      (K.cornerPoint c) (N.cornerOnIncidentXYEdge c)
    cornerXZ : (c : K.Corner3) →
      restriction (N.edgeFirstFace (N.incidentXZEdge (N.cornerIncidentEdges c))) (K.cornerPoint c)
        (N.onFirstFace (N.cornerOnIncidentXZEdge c))
      ≡ restriction (N.edgeSecondFace (N.incidentXZEdge (N.cornerIncidentEdges c))) (K.cornerPoint c)
        (N.onSecondFace (N.cornerOnIncidentXZEdge c))
    cornerXZ c = edgeAgreement (N.incidentXZEdge (N.cornerIncidentEdges c))
      (K.cornerPoint c) (N.cornerOnIncidentXZEdge c)
    cornerYZ : (c : K.Corner3) →
      restriction (N.edgeFirstFace (N.incidentYZEdge (N.cornerIncidentEdges c))) (K.cornerPoint c)
        (N.onFirstFace (N.cornerOnIncidentYZEdge c))
      ≡ restriction (N.edgeSecondFace (N.incidentYZEdge (N.cornerIncidentEdges c))) (K.cornerPoint c)
        (N.onSecondFace (N.cornerOnIncidentYZEdge c))
    cornerYZ c = edgeAgreement (N.incidentYZEdge (N.cornerIncidentEdges c))
      (K.cornerPoint c) (N.cornerOnIncidentYZEdge c)

-- Local stalks preserve each correction. All restrictions agree on one
-- actual selected quotient; centre uses the global section directly.
-- This is a finite offset-fibre Cech consumer, not full physical or
-- Monster X6 action. Source-written; kernel pending.
