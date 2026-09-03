module DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound13Exact where

------------------------------------------------------------------------
-- ROUND 13: SIX FACE-ATTACHED HYPERCUBES + THREE-FACE CORNER INCIDENCE
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

record Round13Status : Set where
  constructor round13Status
  field
    sixLiteralOuterFacesOwned : Bool
    sixHeisenbergAxesOwned : Bool
    face6ToAxis6TwoSided : Bool
    eachFaceIndexesX6Hypercube : Bool
    faceCoordinateCubeEquivalentToX6 : Bool
    everyCornerSelectsExactlyThreeIncidentFaces : Bool
    cornerIncidenceUsesExistingOnFaceGeometry : Bool
    faceAttachedHypercubesHaveActualMonsterGluing : Bool
    outerFin90CompletedTenTritSquareRecognition : Bool
    actualZetaRecognition : Bool
    fixedRegularBlockRecognition : Bool
    literalResidualFiftyThree : Bool

canonicalRound13Status : Round13Status
canonicalRound13Status =
  round13Status
    true   -- Face6 already literal in T^3 geometry
    true   -- Axis6 already literal in X6 model
    true   -- explicit Face6 <-> Axis6 chart
    true   -- face-indexed AttachedHypercube face = X6
    true   -- six face coordinates are a two-sided X6 chart
    true   -- one x, one y, one z face per corner
    true   -- each incidence proved by Geometry.OnFace
    false  -- live: no actual Monster gluing supplied by geometry alone
    false  -- existing multiplicity recognition frontier remains live
    false  -- existing literal zeta recognition remains live
    false  -- fixed-sector regular block remains live
    false  -- residual follows that split

data SearchClass : Set where
  OWNED GENERATED LIVE DOWNSTREAM PRUNED PARALLEL : SearchClass

faceGeometryClass : SearchClass
faceGeometryClass = OWNED

faceAxisChartClass : SearchClass
faceAxisChartClass = OWNED

faceIndexedHypercubeClass : SearchClass
faceIndexedHypercubeClass = OWNED

cornerThreeFaceIncidenceClass : SearchClass
cornerThreeFaceIncidenceClass = OWNED

actualFaceHypercubeGluingClass : SearchClass
actualFaceHypercubeGluingClass = LIVE

multiplicityRecognitionClass : SearchClass
multiplicityRecognitionClass = LIVE

zetaRecognitionClass : SearchClass
zetaRecognitionClass = LIVE

fixedRegularClass : SearchClass
fixedRegularClass = LIVE

literalResidual53Class : SearchClass
literalResidual53Class = DOWNSTREAM

------------------------------------------------------------------------
-- Decisive Round-13 picture:
--
--                  x-/x+
--                    |
--       z-/z+ ---- Corner ---- y-/y+
--
-- A corner chooses one face from each opposite pair, hence exactly three
-- incident faces.  The six face labels are simultaneously a two-sided chart
-- for the six coordinates of X6 = T^6.  Thus the 27-cube boundary and the
-- 729-state Heisenberg hypercube now share a typed face/axis interface.
--
-- What is NOT yet owned is a physical/Monster gluing law saying how the six
-- face-indexed X6 fibres attach across common edges/corners inside the literal
-- VOA action.  That is the next scientific promotion target.
------------------------------------------------------------------------
