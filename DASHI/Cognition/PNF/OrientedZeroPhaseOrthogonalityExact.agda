module DASHI.Cognition.PNF.OrientedZeroPhaseOrthogonalityExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.OrientedZeroFutureQuotientExact as Wave
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel
import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection

------------------------------------------------------------------------
-- LOCAL ORIENTATION PHASE IS A FOURTH, FIBRE-LOCAL COORDINATE
--
-- It is distinct from representation modality, C3 process/task phase, and
-- evidence-derived semantic phase.  The orientation coordinate only exists on
-- the scalar-zero fibre.
------------------------------------------------------------------------

record ZeroPhaseState : Set where
  constructor zeroPhaseState
  field
    orientation : Wave.ZeroOrientation
    processPhase : Wheel.DepthWheelPhase
    semanticPhase : Selection.InteractionDirection

open ZeroPhaseState public

flipOrientation : ZeroPhaseState → ZeroPhaseState
flipOrientation state with orientation state
... | Wave.approachingZero =
  zeroPhaseState Wave.leavingZero (processPhase state) (semanticPhase state)
... | Wave.leavingZero =
  zeroPhaseState Wave.approachingZero (processPhase state) (semanticPhase state)

advanceProcess : ZeroPhaseState → ZeroPhaseState
advanceProcess state =
  zeroPhaseState
    (orientation state)
    (Wheel.nextDepthWheelPhase (processPhase state))
    (semanticPhase state)

orientationFlipPreservesProcessPhase :
  (state : ZeroPhaseState) →
  processPhase (flipOrientation state) ≡ processPhase state
orientationFlipPreservesProcessPhase (zeroPhaseState Wave.approachingZero phase semantic) = refl
orientationFlipPreservesProcessPhase (zeroPhaseState Wave.leavingZero phase semantic) = refl

orientationFlipPreservesSemanticPhase :
  (state : ZeroPhaseState) →
  semanticPhase (flipOrientation state) ≡ semanticPhase state
orientationFlipPreservesSemanticPhase (zeroPhaseState Wave.approachingZero phase semantic) = refl
orientationFlipPreservesSemanticPhase (zeroPhaseState Wave.leavingZero phase semantic) = refl

processAdvancePreservesOrientation :
  (state : ZeroPhaseState) →
  orientation (advanceProcess state) ≡ orientation state
processAdvancePreservesOrientation state = refl

orientationAndProcessAdvanceCommute :
  (state : ZeroPhaseState) →
  flipOrientation (advanceProcess state) ≡ advanceProcess (flipOrientation state)
orientationAndProcessAdvanceCommute (zeroPhaseState Wave.approachingZero phase semantic) = refl
orientationAndProcessAdvanceCommute (zeroPhaseState Wave.leavingZero phase semantic) = refl

------------------------------------------------------------------------
-- Adaptive carrier: orientation data is present only at scalar zero.
------------------------------------------------------------------------

data LocalOrientationFibre : Wave.Scalar3 → Set where
  negativeSingleton : LocalOrientationFibre Wave.negative
  zeroOrientation : Wave.ZeroOrientation → LocalOrientationFibre Wave.scalarZero
  positiveSingleton : LocalOrientationFibre Wave.positive

waveOrientationFibre :
  (state : Wave.Wave4) → LocalOrientationFibre (Wave.scalar state)
waveOrientationFibre Wave.negativeOne = negativeSingleton
waveOrientationFibre Wave.negativeZero = zeroOrientation Wave.approachingZero
waveOrientationFibre Wave.positiveZero = zeroOrientation Wave.leavingZero
waveOrientationFibre Wave.positiveOne = positiveSingleton

------------------------------------------------------------------------
-- This is fibre-local phase refinement: only a dynamically nontrivial coarse
-- fibre pays for the additional orientation coordinate.
------------------------------------------------------------------------
