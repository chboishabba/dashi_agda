module DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridgeRegression where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Foundations.SSPPrimeLane369Refinement as Ref
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

------------------------------------------------------------------------
-- Regression pins for the depthwise-wheel interpretation.

regression-one-wheel-closes-at-three :
  Wheel.depthWheelPhase Ref.three ≡ Wheel.phase-0
regression-one-wheel-closes-at-three = Wheel.threeDepthIsOneWheel

regression-two-wheels-close-at-six :
  Wheel.depthWheelPhase Ref.six ≡ Wheel.phase-0
regression-two-wheels-close-at-six = Wheel.sixDepthIsTwoWheels

regression-three-wheels-close-at-nine :
  Wheel.depthWheelPhase Ref.nine ≡ Wheel.phase-0
regression-three-wheels-close-at-nine = Wheel.nineDepthIsThreeWheels

regression-three-phase-carrier-count :
  Wheel.listLength Wheel.depthPhaseAtlas ≡ Ref.three
regression-three-phase-carrier-count = Wheel.depthPhaseAtlasCount

regression-polar-phase-carrier-count :
  Wheel.listLength Wheel.polarPhaseAtlas ≡ Ref.six
regression-polar-phase-carrier-count = Wheel.polarPhaseAtlasCount

regression-full-phase-carrier-count :
  Wheel.listLength Wheel.fullPhaseAtlas ≡ Ref.nine
regression-full-phase-carrier-count = Wheel.fullPhaseAtlasCount

regression-canonical-369-address-is-phase-zero :
  Wheel.phase Wheel.canonicalThreeSixNineTaggedAddress ≡ Wheel.phase-0
regression-canonical-369-address-is-phase-zero =
  Wheel.canonicalThreeSixNineTaggedPhaseIsZero

regression-existing-depth-bridge-closes-one-wheel :
  Wheel.refinementWheelPhase Wheel.canonicalThreeSixNineDepthWheelCantorBridge
  ≡ Wheel.phase-0
regression-existing-depth-bridge-closes-one-wheel =
  Wheel.canonicalThreeSixNineWheelPhaseIsZero
