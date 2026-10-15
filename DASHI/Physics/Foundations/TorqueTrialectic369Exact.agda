module DASHI.Physics.Foundations.TorqueTrialectic369Exact where

------------------------------------------------------------------------
-- TORQUE AS AN ORIENTED TRIALECTIC / PANTS SYNTHESIS
--
-- The repository already owns the ingredients separately:
--
--   * 3 x 3 = 9 ordered SO(3) operator slots;
--   * the two-sheet orientation lift of that operator sheet;
--   * 3 x 3 x 3 = 27 bracket voxels;
--   * ordered ternary comparison + synthesis cells (a,b,s);
--   * depth-three ternary pants paths;
--   * balanced ternary and exact C3 Fourier conjugation.
--
-- This module is the physical torque specialization.  A bracket voxel is
-- ordered as (output axis, lever axis, force axis).  The Levi-Civita
-- orientation is a classifier into {-1,0,+1}; it is NOT the torque magnitude.
-- Reversing lever and force negates the orientation and conjugates the C3
-- phase.  The ordered comparison edge is retained when the synthesis face is
-- filled, matching the existing trialectic rule that synthesis does not erase
-- the tension/boundary that produced it.
--
-- No cardinality-only identification is made between the distinct 27-state
-- carriers.  Explicit recharting functions are supplied where needed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Algebra.TriadicDepthOneCharacters as C3Base
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369MobiusTransport as Mobius
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Physics.Closure.SU2SO3369HypervoxelBridge as SO3
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Synthesis
import DASHI.Reasoning.TernarySynthesisCellComplexExact as Cells
import DASHI.Moonshine.JInvariantColourWheelNineSheetPantsGluingExact as Pants369
import DASHI.Moonshine.C3FourierConjugationExact as C3
import DASHI.Topology.TernaryPantsFrontierExact as Frontier

------------------------------------------------------------------------
-- 1. Existing SO(3) 9 / 18 / 27 geometry, now with a typed bracket voxel.
------------------------------------------------------------------------

BracketVoxel : Set
BracketVoxel = SO3.SU2Axis × (SO3.SU2Axis × SO3.SU2Axis)

outputAxis : BracketVoxel → SO3.SU2Axis
outputAxis = proj₁

leverAxis : BracketVoxel → SO3.SU2Axis
leverAxis voxel = proj₁ (proj₂ voxel)

forceAxis : BracketVoxel → SO3.SU2Axis
forceAxis voxel = proj₂ (proj₂ voxel)

torqueOperatorSlot : BracketVoxel → SO3.MatrixSlot
torqueOperatorSlot voxel = leverAxis voxel , forceAxis voxel

operatorSheetCountIsNine : SO3.operatorSheetCount ≡ 9
operatorSheetCountIsNine = SO3.operatorSheetCountIs9

liftedOperatorSheetCountIsEighteen : SO3.liftedOperatorSheetCount ≡ 18
liftedOperatorSheetCountIsEighteen = SO3.liftedOperatorSheetCountIs18

bracketVoxelCountIsTwentySeven : SO3.bracketVoxelCount ≡ 27
bracketVoxelCountIsTwentySeven = SO3.bracketVoxelCountIs27

------------------------------------------------------------------------
-- 2. Levi-Civita orientation as a balanced-ternary classifier.
--
-- Positive triples are the cyclic orientations (x,y,z), (y,z,x), (z,x,y).
-- Negative triples are their reversals.  Repeated-axis triples are neutral.
------------------------------------------------------------------------

torqueOrientation : BracketVoxel → BT.Trit

torqueOrientation (Hyper.axis-low , (Hyper.axis-low , Hyper.axis-low)) = BT.zero
torqueOrientation (Hyper.axis-low , (Hyper.axis-low , Hyper.axis-mid)) = BT.zero
torqueOrientation (Hyper.axis-low , (Hyper.axis-low , Hyper.axis-high)) = BT.zero
torqueOrientation (Hyper.axis-low , (Hyper.axis-mid , Hyper.axis-low)) = BT.zero
torqueOrientation (Hyper.axis-low , (Hyper.axis-mid , Hyper.axis-mid)) = BT.zero
torqueOrientation (Hyper.axis-low , (Hyper.axis-mid , Hyper.axis-high)) = BT.pos
torqueOrientation (Hyper.axis-low , (Hyper.axis-high , Hyper.axis-low)) = BT.zero
torqueOrientation (Hyper.axis-low , (Hyper.axis-high , Hyper.axis-mid)) = BT.neg
torqueOrientation (Hyper.axis-low , (Hyper.axis-high , Hyper.axis-high)) = BT.zero

torqueOrientation (Hyper.axis-mid , (Hyper.axis-low , Hyper.axis-low)) = BT.zero
torqueOrientation (Hyper.axis-mid , (Hyper.axis-low , Hyper.axis-mid)) = BT.zero
torqueOrientation (Hyper.axis-mid , (Hyper.axis-low , Hyper.axis-high)) = BT.neg
torqueOrientation (Hyper.axis-mid , (Hyper.axis-mid , Hyper.axis-low)) = BT.zero
torqueOrientation (Hyper.axis-mid , (Hyper.axis-mid , Hyper.axis-mid)) = BT.zero
torqueOrientation (Hyper.axis-mid , (Hyper.axis-mid , Hyper.axis-high)) = BT.zero
torqueOrientation (Hyper.axis-mid , (Hyper.axis-high , Hyper.axis-low)) = BT.pos
torqueOrientation (Hyper.axis-mid , (Hyper.axis-high , Hyper.axis-mid)) = BT.zero
torqueOrientation (Hyper.axis-mid , (Hyper.axis-high , Hyper.axis-high)) = BT.zero

torqueOrientation (Hyper.axis-high , (Hyper.axis-low , Hyper.axis-low)) = BT.zero
torqueOrientation (Hyper.axis-high , (Hyper.axis-low , Hyper.axis-mid)) = BT.pos
torqueOrientation (Hyper.axis-high , (Hyper.axis-low , Hyper.axis-high)) = BT.zero
torqueOrientation (Hyper.axis-high , (Hyper.axis-mid , Hyper.axis-low)) = BT.neg
torqueOrientation (Hyper.axis-high , (Hyper.axis-mid , Hyper.axis-mid)) = BT.zero
torqueOrientation (Hyper.axis-high , (Hyper.axis-mid , Hyper.axis-high)) = BT.zero
torqueOrientation (Hyper.axis-high , (Hyper.axis-high , Hyper.axis-low)) = BT.zero
torqueOrientation (Hyper.axis-high , (Hyper.axis-high , Hyper.axis-mid)) = BT.zero
torqueOrientation (Hyper.axis-high , (Hyper.axis-high , Hyper.axis-high)) = BT.zero

swapTorqueInputs : BracketVoxel → BracketVoxel
swapTorqueInputs (output , (lever , force)) = output , (force , lever)

swapTorqueInputsInvolutive :
  (voxel : BracketVoxel) →
  swapTorqueInputs (swapTorqueInputs voxel) ≡ voxel
swapTorqueInputsInvolutive (output , (lever , force)) = refl

swapTorqueInputsNegatesOrientation :
  (voxel : BracketVoxel) →
  torqueOrientation (swapTorqueInputs voxel)
  ≡ BT.negate (torqueOrientation voxel)
swapTorqueInputsNegatesOrientation
  (Hyper.axis-low , (Hyper.axis-low , Hyper.axis-low)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-low , (Hyper.axis-low , Hyper.axis-mid)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-low , (Hyper.axis-low , Hyper.axis-high)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-low , (Hyper.axis-mid , Hyper.axis-low)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-low , (Hyper.axis-mid , Hyper.axis-mid)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-low , (Hyper.axis-mid , Hyper.axis-high)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-low , (Hyper.axis-high , Hyper.axis-low)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-low , (Hyper.axis-high , Hyper.axis-mid)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-low , (Hyper.axis-high , Hyper.axis-high)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-mid , (Hyper.axis-low , Hyper.axis-low)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-mid , (Hyper.axis-low , Hyper.axis-mid)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-mid , (Hyper.axis-low , Hyper.axis-high)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-mid , (Hyper.axis-mid , Hyper.axis-low)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-mid , (Hyper.axis-mid , Hyper.axis-mid)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-mid , (Hyper.axis-mid , Hyper.axis-high)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-mid , (Hyper.axis-high , Hyper.axis-low)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-mid , (Hyper.axis-high , Hyper.axis-mid)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-mid , (Hyper.axis-high , Hyper.axis-high)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-high , (Hyper.axis-low , Hyper.axis-low)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-high , (Hyper.axis-low , Hyper.axis-mid)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-high , (Hyper.axis-low , Hyper.axis-high)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-high , (Hyper.axis-mid , Hyper.axis-low)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-high , (Hyper.axis-mid , Hyper.axis-mid)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-high , (Hyper.axis-mid , Hyper.axis-high)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-high , (Hyper.axis-high , Hyper.axis-low)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-high , (Hyper.axis-high , Hyper.axis-mid)) = refl
swapTorqueInputsNegatesOrientation
  (Hyper.axis-high , (Hyper.axis-high , Hyper.axis-high)) = refl

------------------------------------------------------------------------
-- 3. Exact C3 / zeta phase chart for the three orientation sectors.
------------------------------------------------------------------------

orientationToPhase : BT.Trit → C3Base.C3Phase
orientationToPhase BT.neg = C3.zetaSquared
orientationToPhase BT.zero = C3.one
orientationToPhase BT.pos = C3.zeta

torquePhase : BracketVoxel → C3Base.C3Phase
torquePhase voxel = orientationToPhase (torqueOrientation voxel)

orientationNegationConjugatesPhase :
  (orientation : BT.Trit) →
  orientationToPhase (BT.negate orientation)
  ≡ C3.inversePhase (orientationToPhase orientation)
orientationNegationConjugatesPhase BT.neg = refl
orientationNegationConjugatesPhase BT.zero = refl
orientationNegationConjugatesPhase BT.pos = refl

swapTorqueInputsConjugatesPhase :
  (voxel : BracketVoxel) →
  torquePhase (swapTorqueInputs voxel)
  ≡ C3.inversePhase (torquePhase voxel)
swapTorqueInputsConjugatesPhase voxel
  rewrite swapTorqueInputsNegatesOrientation voxel =
  orientationNegationConjugatesPhase (torqueOrientation voxel)

------------------------------------------------------------------------
-- 4. The same bracket voxel as ordered comparison + synthesis face.
------------------------------------------------------------------------

torqueComparison : BracketVoxel → Synthesis.Comparison9
torqueComparison voxel =
  SO3.axisToTriTruth (leverAxis voxel)
  , SO3.axisToTriTruth (forceAxis voxel)

torqueSynthesisChoice : BracketVoxel → Synthesis.SynthesisChoice27
torqueSynthesisChoice voxel =
  Synthesis.makeSynthesisChoice
    (SO3.axisToTriTruth (leverAxis voxel))
    (SO3.axisToTriTruth (forceAxis voxel))
    (SO3.axisToTriTruth (outputAxis voxel))

torqueSynthesisTwoCell : BracketVoxel → Cells.LocalSynthesisTwoCell
torqueSynthesisTwoCell voxel =
  Cells.choiceToTwoCell (torqueSynthesisChoice voxel)

torqueFaceRetainsComparison :
  (voxel : BracketVoxel) →
  Cells.originalComparisonEdge (torqueSynthesisTwoCell voxel)
  ≡ Cells.comparisonOneCell (torqueComparison voxel)
torqueFaceRetainsComparison (output , (lever , force)) = refl

------------------------------------------------------------------------
-- 5. Explicit rechart to the existing depth-three pants / 27-point carrier.
------------------------------------------------------------------------

axisToSSP : SO3.SU2Axis → SSP.SSPTrit
axisToSSP Hyper.axis-low = SSP.sspNegOne
axisToSSP Hyper.axis-mid = SSP.sspZero
axisToSSP Hyper.axis-high = SSP.sspPosOne

torqueVoxelPoint : BracketVoxel → Fabric.Ternary27Point
torqueVoxelPoint voxel =
  Fabric.ternary27Point
    (axisToSSP (leverAxis voxel))
    (axisToSSP (forceAxis voxel))
    (axisToSSP (outputAxis voxel))

torquePantsPath : BracketVoxel → Frontier.PantsPath 3
torquePantsPath voxel =
  Pants369.voxel27ToPants3 (torqueVoxelPoint voxel)

torquePantsRoundTrip :
  (voxel : BracketVoxel) →
  Pants369.pants3ToVoxel27 (torquePantsPath voxel)
  ≡ torqueVoxelPoint voxel
torquePantsRoundTrip voxel =
  Pants369.voxelPantsRoundTrip (torqueVoxelPoint voxel)

------------------------------------------------------------------------
-- 6. Common physical carrier.  Geometry/orientation and amplitude are separate.
------------------------------------------------------------------------

record OrientedTorque (TorqueValue : Set) : Set₁ where
  constructor oriented-torque
  field
    geometry : BracketVoxel
    value : TorqueValue

open OrientedTorque public

orientedTorqueOrientation :
  ∀ {TorqueValue} → OrientedTorque TorqueValue → BT.Trit
orientedTorqueOrientation torque = torqueOrientation (geometry torque)

orientedTorquePhase :
  ∀ {TorqueValue} → OrientedTorque TorqueValue → C3Base.C3Phase
orientedTorquePhase torque = torquePhase (geometry torque)

orientedTorqueFace :
  ∀ {TorqueValue} → OrientedTorque TorqueValue → Cells.LocalSynthesisTwoCell
orientedTorqueFace torque = torqueSynthesisTwoCell (geometry torque)

record TorqueMagnitudeWitness
    (Scalar TorqueValue : Set)
    (torque : OrientedTorque TorqueValue) : Set₁ where
  constructor torque-magnitude-witness
  field
    magnitudeOf : TorqueValue → Scalar
    amplitude : Scalar
    amplitudeExact : magnitudeOf (value torque) ≡ amplitude

open TorqueMagnitudeWitness public

------------------------------------------------------------------------
-- 7. Nonzero orientation can use the existing two-sheet lift; zero remains a
-- separate neutral sector and is not silently forced into either lift.
------------------------------------------------------------------------

data NonzeroTorqueOrientation (voxel : BracketVoxel) : Set where
  positiveTorque :
    torqueOrientation voxel ≡ BT.pos →
    NonzeroTorqueOrientation voxel
  negativeTorque :
    torqueOrientation voxel ≡ BT.neg →
    NonzeroTorqueOrientation voxel

orientationLift :
  {voxel : BracketVoxel} →
  NonzeroTorqueOrientation voxel →
  Mobius.OrientationPolarity
orientationLift (positiveTorque _) = Mobius.positive
orientationLift (negativeTorque _) = Mobius.negative

------------------------------------------------------------------------
-- 8. Authority boundary: exact structural claims only.
------------------------------------------------------------------------

record TorqueTrialectic369AuthorityBoundary : Set where
  constructor torque-trialectic-369-authority-boundary
  field
    existingNineOperatorSheetReused : Bool
    existingEighteenLiftedSheetReused : Bool
    existingTwentySevenBracketCountReused : Bool
    balancedTernaryIsOrientationNotMagnitude : Bool
    synthesisFaceRetainsComparisonBoundary : Bool
    depthThreePantsRechartIsExplicit : Bool
    reversalNegatesOrientation : Bool
    reversalConjugatesC3Phase : Bool
    zeroOrientationForcedIntoTwoSheetLift : Bool
    distinctTwentySevenCarriersIdentifiedByCardinalityAlone : Bool

canonicalTorqueTrialectic369AuthorityBoundary :
  TorqueTrialectic369AuthorityBoundary
canonicalTorqueTrialectic369AuthorityBoundary =
  torque-trialectic-369-authority-boundary
    true
    true
    true
    true
    true
    true
    true
    true
    false
    false
