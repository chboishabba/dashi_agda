module DASHI.Physics.Foundations.OrientedThreeAxisBracket369Exact where

------------------------------------------------------------------------
-- GENERIC ORIENTED THREE-AXIS BRACKET / 369 RECHART
--
-- This is the mechanism-neutral extraction of the finite geometry first made
-- explicit by TorqueTrialectic369Exact.  It deliberately reuses that already-
-- paid owner instead of duplicating the 27-case Levi-Civita table.
--
-- The generic layer owns only:
--   * an ordered (output,left,right) three-axis bracket voxel;
--   * balanced-ternary orientation {-1,0,+1};
--   * exact C3/zeta phase chart and conjugation under input reversal;
--   * the existing synthesis-face and depth-three pants rechart.
--
-- It does NOT identify amplitudes or mechanisms across torque, electromagnetism,
-- Yang--Mills, or Navier--Stokes.  Domain modules must provide their own value
-- laws and same-object receipts.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Algebra.TriadicDepthOneCharacters as C3Base
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper
import DASHI.Physics.Closure.SU2SO3369HypervoxelBridge as SO3
import DASHI.Physics.Foundations.TorqueTrialectic369Exact as Torque
import DASHI.Reasoning.TernarySynthesisCellComplexExact as Cells
import DASHI.Topology.TernaryPantsFrontierExact as Frontier
import DASHI.Moonshine.C3FourierConjugationExact as C3

BracketVoxel : Set
BracketVoxel = Torque.BracketVoxel

outputAxis : BracketVoxel → SO3.SU2Axis
outputAxis = Torque.outputAxis

leftAxis : BracketVoxel → SO3.SU2Axis
leftAxis = Torque.leverAxis

rightAxis : BracketVoxel → SO3.SU2Axis
rightAxis = Torque.forceAxis

bracketOrientation : BracketVoxel → BT.Trit
bracketOrientation = Torque.torqueOrientation

bracketPhase : BracketVoxel → C3Base.C3Phase
bracketPhase = Torque.torquePhase

inverseBracketPhase : C3Base.C3Phase → C3Base.C3Phase
inverseBracketPhase = C3.inversePhase

swapBracketInputs : BracketVoxel → BracketVoxel
swapBracketInputs = Torque.swapTorqueInputs

swapBracketInputsInvolutive :
  (voxel : BracketVoxel) →
  swapBracketInputs (swapBracketInputs voxel) ≡ voxel
swapBracketInputsInvolutive = Torque.swapTorqueInputsInvolutive

swapBracketInputsNegatesOrientation :
  (voxel : BracketVoxel) →
  bracketOrientation (swapBracketInputs voxel)
  ≡ BT.negate (bracketOrientation voxel)
swapBracketInputsNegatesOrientation =
  Torque.swapTorqueInputsNegatesOrientation

swapBracketInputsConjugatesPhase :
  (voxel : BracketVoxel) →
  bracketPhase (swapBracketInputs voxel)
  ≡ inverseBracketPhase (bracketPhase voxel)
swapBracketInputsConjugatesPhase =
  Torque.swapTorqueInputsConjugatesPhase

bracketFace : BracketVoxel → Cells.LocalSynthesisTwoCell
bracketFace = Torque.torqueSynthesisTwoCell

bracketFaceRetainsOrderedBoundary :
  (voxel : BracketVoxel) →
  Cells.originalComparisonEdge (bracketFace voxel)
  ≡ Cells.comparisonOneCell (Torque.torqueComparison voxel)
bracketFaceRetainsOrderedBoundary = Torque.torqueFaceRetainsComparison

bracketPantsPath : BracketVoxel → Frontier.PantsPath 3
bracketPantsPath = Torque.torquePantsPath

------------------------------------------------------------------------
-- Canonical axis triples used by right-hand-rule and bracket consumers.
-- axis-low/mid/high are only an exact three-axis coordinate chart here.
------------------------------------------------------------------------

xAxis yAxis zAxis : SO3.SU2Axis
xAxis = Hyper.axis-low
yAxis = Hyper.axis-mid
zAxis = Hyper.axis-high

xyzBracket xzyBracket xxyBracket : BracketVoxel
xyzBracket = xAxis , (yAxis , zAxis)
xzyBracket = xAxis , (zAxis , yAxis)
xxyBracket = xAxis , (xAxis , yAxis)

xyzOrientationPositive : bracketOrientation xyzBracket ≡ BT.pos
xyzOrientationPositive = refl

xzyOrientationNegative : bracketOrientation xzyBracket ≡ BT.neg
xzyOrientationNegative = refl

xxyOrientationNeutral : bracketOrientation xxyBracket ≡ BT.zero
xxyOrientationNeutral = refl

------------------------------------------------------------------------
-- Domain values stay separate from the finite orientation address.
------------------------------------------------------------------------

record OrientedBracketSample
    (Left Right Result : Set) : Set₁ where
  constructor oriented-bracket-sample
  field
    geometry : BracketVoxel
    leftValue : Left
    rightValue : Right
    resultValue : Result

open OrientedBracketSample public

sampleOrientation :
  ∀ {Left Right Result} →
  OrientedBracketSample Left Right Result → BT.Trit
sampleOrientation sample = bracketOrientation (geometry sample)

samplePhase :
  ∀ {Left Right Result} →
  OrientedBracketSample Left Right Result → C3Base.C3Phase
samplePhase sample = bracketPhase (geometry sample)

sampleFace :
  ∀ {Left Right Result} →
  OrientedBracketSample Left Right Result → Cells.LocalSynthesisTwoCell
sampleFace sample = bracketFace (geometry sample)

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record OrientedThreeAxisBracket369Boundary : Set where
  constructor oriented-three-axis-bracket-369-boundary
  field
    existingTorqueFiniteGeometryReused : Bool
    balancedTernaryIsOrientationOnly : Bool
    c3PhaseIsFiniteOrientationChart : Bool
    reversalConjugatesFinitePhase : Bool
    synthesisFaceRetainsOrderedBoundary : Bool
    depthThreePantsRechartReused : Bool
    crossDomainAmplitudesIdentifiedAutomatically : Bool
    crossDomainPhysicalMechanismsIdentifiedAutomatically : Bool

canonicalOrientedThreeAxisBracket369Boundary :
  OrientedThreeAxisBracket369Boundary
canonicalOrientedThreeAxisBracket369Boundary =
  oriented-three-axis-bracket-369-boundary
    true true true true true true false false
