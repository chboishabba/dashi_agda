module DASHI.Analysis.PickoverSignedZeroTorque369GridExact where

------------------------------------------------------------------------
-- Reuse existing 3x3 torque sheet, 27 bracket cube and signed-zero fibre.
-- This is a finite structural chart, NOT an analytic sine sign oracle.
-- Primary local sources: TorqueTrialectic369Exact,
-- SignedZeroTernaryOrientationExact, OrientedZeroJetTransitionExact.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Foundations.TorqueTrialectic369Exact as Torque
import DASHI.Physics.Closure.SU2SO3369HypervoxelBridge as SO3
import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper
import DASHI.Algebra.BalancedTernary as BT
import DASHI.Foundations.SignedZeroTernaryOrientationExact as Zero
import DASHI.Moonshine.C3FourierConjugationExact as Fourier

-- An ordered 3x3 operator sheet, not a cyclic C9 group.
Grid9 : Set
Grid9 = SO3.MatrixSlot

-- The original 3x3x3 bracket cube: (output, lever, force).
Cube27 : Set
Cube27 = Torque.BracketVoxel

projectGrid9 : Cube27 → Grid9
projectGrid9 = Torque.torqueOperatorSlot

liftGridWithOutput : SO3.SU2Axis → Grid9 → Cube27
liftGridWithOutput output (lever , force) = output , (lever , force)

projectLift : (output : SO3.SU2Axis) (grid : Grid9) →
  projectGrid9 (liftGridWithOutput output grid) ≡ grid
projectLift output (lever , force) = refl

liftProjection : (cube : Cube27) →
  liftGridWithOutput (Torque.outputAxis cube) (projectGrid9 cube) ≡ cube
liftProjection (output , (lever , force)) = refl

swapGrid : Grid9 → Grid9
swapGrid (lever , force) = force , lever

projectTorqueSwap : (cube : Cube27) →
  projectGrid9 (Torque.swapTorqueInputs cube)
  ≡ swapGrid (projectGrid9 cube)
projectTorqueSwap (output , (lever , force)) = refl

torqueSwapNegates : (cube : Cube27) →
  Torque.torqueOrientation (Torque.swapTorqueInputs cube)
  ≡ BT.negate (Torque.torqueOrientation cube)
torqueSwapNegates = Torque.swapTorqueInputsNegatesOrientation

torqueSwapConjugates : (cube : Cube27) →
  Torque.torquePhase (Torque.swapTorqueInputs cube)
  ≡ Fourier.inversePhase (Torque.torquePhase cube)
torqueSwapConjugates = Torque.swapTorqueInputsConjugatesPhase

-- Translate only the three finite orientation labels to the EXISTING
-- signed-neutral chart. Do not identify scalar zero with physical torque.
toSignedZeroChart : BT.Trit → Zero.SignedNeutralPhase3
toSignedZeroChart BT.neg = Zero.minusZeroPhase
toSignedZeroChart BT.zero = Zero.neutralZeroPhase
toSignedZeroChart BT.pos = Zero.plusZeroPhase

reverseSignedZero : Zero.SignedNeutralPhase3 → Zero.SignedNeutralPhase3
reverseSignedZero Zero.minusZeroPhase = Zero.plusZeroPhase
reverseSignedZero Zero.neutralZeroPhase = Zero.neutralZeroPhase
reverseSignedZero Zero.plusZeroPhase = Zero.minusZeroPhase

chartNegates : (sign : BT.Trit) →
  toSignedZeroChart (BT.negate sign)
  ≡ reverseSignedZero (toSignedZeroChart sign)
chartNegates BT.neg = refl
chartNegates BT.zero = refl
chartNegates BT.pos = refl

signedTorqueSwap : (cube : Cube27) →
  toSignedZeroChart (Torque.torqueOrientation (Torque.swapTorqueInputs cube))
  ≡ reverseSignedZero (toSignedZeroChart (Torque.torqueOrientation cube))
signedTorqueSwap cube
  rewrite Torque.swapTorqueInputsNegatesOrientation cube =
  chartNegates (Torque.torqueOrientation cube)

centreGrid : Grid9
centreGrid = Hyper.axis-mid , Hyper.axis-mid

centreCube : Cube27
centreCube = Hyper.axis-mid , (Hyper.axis-mid , Hyper.axis-mid)

centreProjects : projectGrid9 centreCube ≡ centreGrid
centreProjects = refl

centreTorqueNeutral : Torque.torqueOrientation centreCube ≡ BT.zero
centreTorqueNeutral = refl

-- Two zero SITES, each with two one-sided approach germs.
-- The same direction has opposite sine sign at 0 and the half turn.
-- A finite lookup convention, not a computed transcendental identity.
data ZeroSite : Set where
  zeroTurn halfTurn : ZeroSite

data Approach : Set where
  fromNegative fromPositive : Approach

signedGermConsumer : ZeroSite → Approach → BT.Trit
signedGermConsumer zeroTurn fromNegative = BT.neg
signedGermConsumer zeroTurn fromPositive = BT.pos
signedGermConsumer halfTurn fromNegative = BT.pos
signedGermConsumer halfTurn fromPositive = BT.neg

oppositeBoundaryGerm : (side : Approach) →
  signedGermConsumer halfTurn side
  ≡ BT.negate (signedGermConsumer zeroTurn side)
oppositeBoundaryGerm fromNegative = refl
oppositeBoundaryGerm fromPositive = refl
