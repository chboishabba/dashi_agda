module DASHI.Combinatorics.Dialectic27PantsNativeGridAdjacencyExact where

------------------------------------------------------------------------
-- REAL GAP CLOSURE: native depth-3 pants-path adjacency,
-- bidirectional graph transport to the existing 27-voxel grid.
--
-- Original owners retained:
--  * DASHI.Topology.TernaryCylinderPantsGeometryExact, BranchSlot;
--  * DASHI.Moonshine.JInvariantColourWheelNineSheetPantsGluingExact,
--    exact voxel27ToPants3/pants3ToVoxel27 round trips;
--  * DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact,
--    strict single-coordinate one-step HypervoxelAdjacent;
--  * DASHI.Combinatorics.GraphColouringHomomorphismCoreExact, GraphHom.
--
-- The pants path graph means ONE of the THREE digit slots changes
-- by one adjacent ternary stage. This is a NEW declared combinatorial
-- adjacency, NOT a smooth pants topology or the physical Rubik group.
-- Equal colours on a joining face are boundary-matching data, NOT
-- the proper graph-colouring inequality rule for adjacent vertices.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)
import DASHI.Topology.TernaryCylinderPantsGeometryExact as Pants
import DASHI.Topology.TernaryPantsFrontierExact as Frontier
import DASHI.Moonshine.JInvariantColourWheelNineSheetPantsGluingExact as Canonical
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Foundations.SSPTritCarrier as Trit
import DASHI.Combinatorics.GraphColouringHomomorphismCoreExact as Graph
import DASHI.Reasoning.Dialectic27ThreeColourPantsSeamExact as Painted

data SlotStep : Pants.BranchSlot → Pants.BranchSlot → Set where
  slot3To6 : SlotStep Pants.slot3 Pants.slot6
  slot6To3 : SlotStep Pants.slot6 Pants.slot3
  slot6To9 : SlotStep Pants.slot6 Pants.slot9
  slot9To6 : SlotStep Pants.slot9 Pants.slot6

-- A native path rule, stated directly on three ordered pants slots.
data PantsGridAdjacent : Frontier.PantsPath 3 → Frontier.PantsPath 3 → Set where
  stepFirst : ∀ {a b y z} →
    SlotStep a b →
    PantsGridAdjacent
      (a vcons y vcons z vcons vnil)
      (b vcons y vcons z vcons vnil)
  stepSecond : ∀ {x a b z} →
    SlotStep a b →
    PantsGridAdjacent
      (x vcons a vcons z vcons vnil)
      (x vcons b vcons z vcons vnil)
  stepThird : ∀ {x y a b} →
    SlotStep a b →
    PantsGridAdjacent
      (x vcons y vcons a vcons vnil)
      (x vcons y vcons b vcons vnil)

cubeGrid : Graph.RelGraph
cubeGrid = Graph.relGraph
  Cube.Ternary27Point Cube.HypervoxelAdjacent

pantsGrid : Graph.RelGraph
pantsGrid = Graph.relGraph
  (Frontier.PantsPath 3) PantsGridAdjacent

-- Twelve constructors: four possible unit ternary steps on each
-- of the three axes. The witnesses are not a transported definition;
-- both graph adjacencies were independently stated in constructors.
voxelStepToNativePantsStep :
  ∀ {left right : Cube.Ternary27Point} →
  Cube.HypervoxelAdjacent left right →
  PantsGridAdjacent
    (Canonical.voxel27ToPants3 left)
    (Canonical.voxel27ToPants3 right)
voxelStepToNativePantsStep (Cube.adjacentX Cube.negToZero) =
  stepFirst slot3To6
voxelStepToNativePantsStep (Cube.adjacentX Cube.zeroToNeg) =
  stepFirst slot6To3
voxelStepToNativePantsStep (Cube.adjacentX Cube.zeroToPos) =
  stepFirst slot6To9
voxelStepToNativePantsStep (Cube.adjacentX Cube.posToZero) =
  stepFirst slot9To6
voxelStepToNativePantsStep (Cube.adjacentY Cube.negToZero) =
  stepSecond slot3To6
voxelStepToNativePantsStep (Cube.adjacentY Cube.zeroToNeg) =
  stepSecond slot6To3
voxelStepToNativePantsStep (Cube.adjacentY Cube.zeroToPos) =
  stepSecond slot6To9
voxelStepToNativePantsStep (Cube.adjacentY Cube.posToZero) =
  stepSecond slot9To6
voxelStepToNativePantsStep (Cube.adjacentZ Cube.negToZero) =
  stepThird slot3To6
voxelStepToNativePantsStep (Cube.adjacentZ Cube.zeroToNeg) =
  stepThird slot6To3
voxelStepToNativePantsStep (Cube.adjacentZ Cube.zeroToPos) =
  stepThird slot6To9
voxelStepToNativePantsStep (Cube.adjacentZ Cube.posToZero) =
  stepThird slot9To6

nativePantsStepToVoxelStep :
  ∀ {left right : Frontier.PantsPath 3} →
  PantsGridAdjacent left right →
  Cube.HypervoxelAdjacent
    (Canonical.pants3ToVoxel27 left)
    (Canonical.pants3ToVoxel27 right)
nativePantsStepToVoxelStep (stepFirst slot3To6) =
  Cube.adjacentX Cube.negToZero
nativePantsStepToVoxelStep (stepFirst slot6To3) =
  Cube.adjacentX Cube.zeroToNeg
nativePantsStepToVoxelStep (stepFirst slot6To9) =
  Cube.adjacentX Cube.zeroToPos
nativePantsStepToVoxelStep (stepFirst slot9To6) =
  Cube.adjacentX Cube.posToZero
nativePantsStepToVoxelStep (stepSecond slot3To6) =
  Cube.adjacentY Cube.negToZero
nativePantsStepToVoxelStep (stepSecond slot6To3) =
  Cube.adjacentY Cube.zeroToNeg
nativePantsStepToVoxelStep (stepSecond slot6To9) =
  Cube.adjacentY Cube.zeroToPos
nativePantsStepToVoxelStep (stepSecond slot9To6) =
  Cube.adjacentY Cube.posToZero
nativePantsStepToVoxelStep (stepThird slot3To6) =
  Cube.adjacentZ Cube.negToZero
nativePantsStepToVoxelStep (stepThird slot6To3) =
  Cube.adjacentZ Cube.zeroToNeg
nativePantsStepToVoxelStep (stepThird slot6To9) =
  Cube.adjacentZ Cube.zeroToPos
nativePantsStepToVoxelStep (stepThird slot9To6) =
  Cube.adjacentZ Cube.posToZero

voxelPantsGridHom : Graph.GraphHom cubeGrid pantsGrid
voxelPantsGridHom =
  Graph.graphHom Canonical.voxel27ToPants3 voxelStepToNativePantsStep

pantsVoxelGridHom : Graph.GraphHom pantsGrid cubeGrid
pantsVoxelGridHom =
  Graph.graphHom Canonical.pants3ToVoxel27 nativePantsStepToVoxelStep

voxelPantsVoxelIdentity : (voxel : Cube.Ternary27Point) →
  Graph.onVertex pantsVoxelGridHom
    (Graph.onVertex voxelPantsGridHom voxel) ≡ voxel
voxelPantsVoxelIdentity = Canonical.voxelPantsRoundTrip

pantsVoxelPantsIdentity : (path : Frontier.PantsPath 3) →
  Graph.onVertex voxelPantsGridHom
    (Graph.onVertex pantsVoxelGridHom path) ≡ path
pantsVoxelPantsIdentity = Canonical.pantsVoxelRoundTrip

-- Proper vertex colouring of the grid is an adjacency HETEROGENEITY
-- demand; equality of face paint is interface HOMOGENEITY. These are
-- different predicates, so the Rubik analogy must not conflate them.
data DifferentPaint : Painted.Paint3 → Painted.Paint3 → Set where
  redGreen : DifferentPaint Painted.red Painted.green
  greenRed : DifferentPaint Painted.green Painted.red
  redBlue : DifferentPaint Painted.red Painted.blue
  blueRed : DifferentPaint Painted.blue Painted.red
  greenBlue : DifferentPaint Painted.green Painted.blue
  blueGreen : DifferentPaint Painted.blue Painted.green

noRedRedDifference : DifferentPaint Painted.red Painted.red → ⊥
noRedRedDifference ()

paintPalette : Graph.RelGraph
paintPalette = Graph.paletteGraph Painted.Paint3 DifferentPaint

constantRed : Cube.Ternary27Point → Painted.Paint3
constantRed _ = Painted.red

-- An identically RED painted pair of faces is a positive same-colour
-- seam fixture, yet a constant-red colouring cannot be a proper
-- colouring of the full 27-grid: neighbouring vertices need DIFFERENT
-- palette colours. This is a concrete counterexample, not a slogan.
constantRedCannotBeProperGridColouring :
  (proper : Graph.GraphHom cubeGrid paintPalette) →
  ((v : Cube.Ternary27Point) →
    Graph.onVertex proper v ≡ constantRed v) →
  ⊥
constantRedCannotBeProperGridColouring proper allRed =
  noRedRedDifference
    (transportEndpoints
      (allRed Cube.negativeCorner)
      (allRed
        (Cube.ternary27Point
          Trit.sspZero Trit.sspNegOne Trit.sspNegOne))
      (Graph.preservesAdj proper Cube.negativeCornerAdjacentXInward))
  where
    transportEndpoints :
      ∀ {a b : Painted.Paint3} →
      a ≡ Painted.red →
      b ≡ Painted.red →
      DifferentPaint a b → DifferentPaint Painted.red Painted.red
    transportEndpoints refl refl edge = edge

-- An explicit PROPER three-colouring of every vertex, unlike the
-- strictly EQUAL paint required on two face-to-face interfaces.
-- It is the C3 sum of the three ternary position indices modulo 3.
-- This is a colouring of our finite GRID graph only.
rotateDifferent : (c : Painted.Paint3) →
  DifferentPaint c (Painted.rotatePaint c)
rotateDifferent Painted.red = redGreen
rotateDifferent Painted.green = greenBlue
rotateDifferent Painted.blue = blueRed

reverseDifferent : ∀ {a b : Painted.Paint3} →
  DifferentPaint a b → DifferentPaint b a
reverseDifferent redGreen = greenRed
reverseDifferent greenRed = redGreen
reverseDifferent redBlue = blueRed
reverseDifferent blueRed = redBlue
reverseDifferent greenBlue = blueGreen
reverseDifferent blueGreen = greenBlue

rotatePreservesDifferent : ∀ {a b : Painted.Paint3} →
  DifferentPaint a b →
  DifferentPaint (Painted.rotatePaint a) (Painted.rotatePaint b)
rotatePreservesDifferent redGreen = greenBlue
rotatePreservesDifferent greenRed = blueGreen
rotatePreservesDifferent redBlue = greenRed
rotatePreservesDifferent blueRed = redGreen
rotatePreservesDifferent greenBlue = blueRed
rotatePreservesDifferent blueGreen = redBlue

shiftColour : Trit.SSPTrit → Painted.Paint3 → Painted.Paint3
shiftColour Trit.sspNegOne c = c
shiftColour Trit.sspZero c = Painted.rotatePaint c
shiftColour Trit.sspPosOne c =
  Painted.rotatePaint (Painted.rotatePaint c)

shiftPreservesDifferent : (t : Trit.SSPTrit) →
  ∀ {a b : Painted.Paint3} →
  DifferentPaint a b →
  DifferentPaint (shiftColour t a) (shiftColour t b)
shiftPreservesDifferent Trit.sspNegOne edge = edge
shiftPreservesDifferent Trit.sspZero edge =
  rotatePreservesDifferent edge
shiftPreservesDifferent Trit.sspPosOne edge =
  rotatePreservesDifferent (rotatePreservesDifferent edge)

threeColourVoxel : Cube.Ternary27Point → Painted.Paint3
threeColourVoxel (Cube.ternary27Point x y z) =
  shiftColour x (shiftColour y (shiftColour z Painted.red))

properThreeColouringPreservesAdjacency :
  ∀ {a b : Cube.Ternary27Point} →
  Cube.HypervoxelAdjacent a b →
  DifferentPaint (threeColourVoxel a) (threeColourVoxel b)
properThreeColouringPreservesAdjacency
  (Cube.adjacentX Cube.negToZero) =
  rotateDifferent _
properThreeColouringPreservesAdjacency
  (Cube.adjacentX Cube.zeroToNeg) =
  reverseDifferent (rotateDifferent _)
properThreeColouringPreservesAdjacency
  (Cube.adjacentX Cube.zeroToPos) =
  rotateDifferent _
properThreeColouringPreservesAdjacency
  (Cube.adjacentX Cube.posToZero) =
  reverseDifferent (rotateDifferent _)
properThreeColouringPreservesAdjacency
  (Cube.adjacentY {x0 = x} Cube.negToZero) =
  shiftPreservesDifferent x (rotateDifferent _)
properThreeColouringPreservesAdjacency
  (Cube.adjacentY {x0 = x} Cube.zeroToNeg) =
  shiftPreservesDifferent x (reverseDifferent (rotateDifferent _))
properThreeColouringPreservesAdjacency
  (Cube.adjacentY {x0 = x} Cube.zeroToPos) =
  shiftPreservesDifferent x (rotateDifferent _)
properThreeColouringPreservesAdjacency
  (Cube.adjacentY {x0 = x} Cube.posToZero) =
  shiftPreservesDifferent x (reverseDifferent (rotateDifferent _))
properThreeColouringPreservesAdjacency
  (Cube.adjacentZ {x0 = x} {y0 = y} Cube.negToZero) =
  shiftPreservesDifferent x
    (shiftPreservesDifferent y (rotateDifferent _))
properThreeColouringPreservesAdjacency
  (Cube.adjacentZ {x0 = x} {y0 = y} Cube.zeroToNeg) =
  shiftPreservesDifferent x
    (shiftPreservesDifferent y
      (reverseDifferent (rotateDifferent _)))
properThreeColouringPreservesAdjacency
  (Cube.adjacentZ {x0 = x} {y0 = y} Cube.zeroToPos) =
  shiftPreservesDifferent x
    (shiftPreservesDifferent y (rotateDifferent _))
properThreeColouringPreservesAdjacency
  (Cube.adjacentZ {x0 = x} {y0 = y} Cube.posToZero) =
  shiftPreservesDifferent x
    (shiftPreservesDifferent y
      (reverseDifferent (rotateDifferent _)))

properThreeColouringOfVoxelGrid : Graph.GraphHom cubeGrid paintPalette
properThreeColouringOfVoxelGrid =
  Graph.graphHom threeColourVoxel properThreeColouringPreservesAdjacency

properThreeColouringOfNativePantsGrid :
  Graph.GraphHom pantsGrid paintPalette
properThreeColouringOfNativePantsGrid =
  Graph.composeHom pantsVoxelGridHom properThreeColouringOfVoxelGrid

-- This exact graph equivalence is for the *declared* native
-- one-slot pants path graph. It does NOT claim that an arbitrary
-- pants-branch wave graph or smooth pair-of-pants graph has
-- this adjacency, or that the user's full semantic 3-colour
-- seam data becomes an adequate sheaf gluing condition.
