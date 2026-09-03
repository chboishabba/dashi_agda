module DASHI.Moonshine.Base369Monster3BRepresentationBidiSearchRound14Exact where

------------------------------------------------------------------------
-- ROUND 14: 6-FACE / 12-EDGE / 8-CORNER CECH GLUING
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

record Round14Status : Set where
  constructor round14Status
  field
    sixFaceBoundaryObjectsOwned : Bool
    twelveLiteralEdgeOverlapsOwned : Bool
    eightLiteralCornerTripleOverlapsOwned : Bool
    everyEdgeHasTwoOnFaceWitnesses : Bool
    everyCornerSelectsXYXZAndYZEdges : Bool
    invertibleEdgeTransportInterfaceOwned : Bool
    cornerCocycleInterfaceOwned : Bool
    modelIdentityGluingOwned : Bool
    zetaRecognitionCompilesActualFixedSliceFaceGluing : Bool
    separateFaceGluingPaymentAfterZetaRecognition : Bool
    fullMonsterNormalizerFaceGluingOwned : Bool
    outerFin90CompletedTenTritSquareRecognition : Bool
    actualZetaRecognition : Bool
    fixedRegularBlockRecognition : Bool
    literalResidualFiftyThree : Bool

canonicalRound14Status : Round14Status
canonicalRound14Status =
  round14Status
    true   -- six literal faces
    true   -- Edge12 = xy/xz/yz sign pairs
    true   -- eight literal Corner3 objects
    true   -- midpoint and corner incidence use Geometry.OnFace
    true   -- each corner chooses one edge of each axis-pair type
    true   -- two-sided edge transports required
    true   -- T_xz = T_yz o T_xy at each corner
    true   -- common X6 action gives identity Cech transitions
    true   -- conditional compiler from ActualZetaSectorRecognition
    false  -- pruned as independent payment after zeta recognition
    false  -- Axis6 translation gluing is not full Monster normalizer gluing
    false  -- multiplicity semantic recognition remains live
    false  -- principal scientific input remains live
    false  -- fixed W_1 regular block remains live
    false  -- literal R53 follows fixed-sector split

------------------------------------------------------------------------
-- Search classes.
------------------------------------------------------------------------

data SearchClass : Set where
  OWNED GENERATED LIVE DOWNSTREAM PRUNED PARALLEL : SearchClass

boundaryNerveClass : SearchClass
boundaryNerveClass = OWNED

edgeTransportClass : SearchClass
edgeTransportClass = OWNED

cornerCocycleClass : SearchClass
cornerCocycleClass = OWNED

modelFaceGluingClass : SearchClass
modelFaceGluingClass = OWNED

actualFaceGluingAfterZetaClass : SearchClass
actualFaceGluingAfterZetaClass = DOWNSTREAM

separateActualFaceGluingSearchClass : SearchClass
separateActualFaceGluingSearchClass = PRUNED

fullMonsterNormalizerGluingClass : SearchClass
fullMonsterNormalizerGluingClass = LIVE

multiplicityRecognitionClass : SearchClass
multiplicityRecognitionClass = LIVE

zetaRecognitionClass : SearchClass
zetaRecognitionClass = LIVE

fixedRegularClass : SearchClass
fixedRegularClass = LIVE

literalResidual53Class : SearchClass
literalResidual53Class = DOWNSTREAM

------------------------------------------------------------------------
-- Decisive Round-14 picture:
--
--   6 faces
--     ^
--     | 12 pairwise edge overlaps
--     ^
--     | 8 triple corner overlaps
--
-- with corner cocycle
--
--   T_xz = T_yz o T_xy.
--
-- Conditional on ActualZetaSectorRecognition, every fixed Fin90 coordinate is
-- one actual X6 slice.  Reusing that SAME slice for all six face charts makes
-- identity edge transitions and the corner cocycle compiler output.  Therefore
-- face gluing is not a new scientific leaf after zeta recognition.
--
-- The actual remaining promotion target is stronger: recognize the semantic
-- 90 ~= Completed10 x T^2 coordinate and recover the fixed-sector regular
-- X6 x Fin90 block so that R53 becomes a literal same-action residual.
------------------------------------------------------------------------
