module DASHI.Biology.Physical.FiniteMorphogeneticBasinControlExact where

------------------------------------------------------------------------
-- Finite quantitative upgrade of GoalErrorDescentControllerExact.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.GoalErrorDescentControllerExact as Descent

data BasinState : Set where
  failed far near target : BasinState

passiveRepair : BasinState → BasinState
passiveRepair failed = failed
passiveRepair far = near
passiveRepair near = target
passiveRepair target = target

repair2 : BasinState → BasinState
repair2 x = passiveRepair (passiveRepair x)

farInTwoStepBasin : repair2 far ≡ target
farInTwoStepBasin = refl

nearInOneStepBasin : passiveRepair near ≡ target
nearInOneStepBasin = refl

targetFixed : passiveRepair target ≡ target
targetFixed = refl

failedOutsidePassiveBasin : repair2 failed ≢ target
failedOutsidePassiveBasin ()

robustnessDepth : BasinState → Nat
robustnessDepth target = 0
robustnessDepth near = 1
robustnessDepth far = 2
robustnessDepth failed = 3

nearMoreRobustThanFar : robustnessDepth near < robustnessDepth far
nearMoreRobustThanFar = s≤s z≤n

data Intervention : Set where
  noControl mildPulse strongPulse : Intervention

controlCost : Intervention → Nat
controlCost noControl = 0
controlCost mildPulse = 1
controlCost strongPulse = 2

controlledStep : Intervention → BasinState → BasinState
controlledStep noControl x = x
controlledStep mildPulse failed = far
controlledStep mildPulse far = near
controlledStep mildPulse near = target
controlledStep mildPulse target = target
controlledStep strongPulse failed = near
controlledStep strongPulse far = target
controlledStep strongPulse near = target
controlledStep strongPulse target = target

strongPulseReachesTargetFromFar : controlledStep strongPulse far ≡ target
strongPulseReachesTargetFromFar = refl

record OneStepTargeting (u : Intervention) : Set where
  constructor oneStepTargeting
  field
    hitsTarget : controlledStep u far ≡ target

open OneStepTargeting public

strongTargeting : OneStepTargeting strongPulse
strongTargeting = oneStepTargeting refl

oneStepTargetingCostsAtLeastTwo :
  (u : Intervention) → OneStepTargeting u → 2 ≤ controlCost u
oneStepTargetingCostsAtLeastTwo noControl (oneStepTargeting ())
oneStepTargetingCostsAtLeastTwo mildPulse (oneStepTargeting ())
oneStepTargetingCostsAtLeastTwo strongPulse p = ≤-refl

strongPulseIsOneStepCostOptimal :
  (u : Intervention) → OneStepTargeting u →
  controlCost strongPulse ≤ controlCost u
strongPulseIsOneStepCostOptimal = oneStepTargetingCostsAtLeastTwo

controlledTwice : Intervention → BasinState → BasinState
controlledTwice u x = controlledStep u (controlledStep u x)

twoMildReachTarget : controlledTwice mildPulse far ≡ target
twoMildReachTarget = refl

sameNominalCostDifferentControlPath :
  controlCost strongPulse ≡ controlCost mildPulse + controlCost mildPulse
sameNominalCostDifferentControlPath = refl

data TargetBasin : Set where
  hand foot eye tail : TargetBasin

data Bit : Set where b0 b1 : Bit

record TwoBits : Set where
  constructor bits
  field first second : Bit

open TwoBits public

encodeTarget : TargetBasin → TwoBits
encodeTarget hand = bits b0 b0
encodeTarget foot = bits b0 b1
encodeTarget eye  = bits b1 b0
encodeTarget tail = bits b1 b1

decodeTarget : TwoBits → TargetBasin
decodeTarget (bits b0 b0) = hand
decodeTarget (bits b0 b1) = foot
decodeTarget (bits b1 b0) = eye
decodeTarget (bits b1 b1) = tail

targetCodeExact : (g : TargetBasin) → decodeTarget (encodeTarget g) ≡ g
targetCodeExact hand = refl
targetCodeExact foot = refl
targetCodeExact eye = refl
targetCodeExact tail = refl

record BasinCalibrationInterface : Set₁ where
  field
    LatentState InterventionData : Set
    encodeMeasurement : InterventionData → LatentState
    empiricalTarget : LatentState → Bool
    empiricalFailure : LatentState → Bool

record BasinAuthorityBoundary : Set where
  field
    finiteDepthEqualsPhysicalDistanceToSeparatrix : Bool
    finiteDepthEqualsPhysicalDistanceToSeparatrixIsFalse :
      finiteDepthEqualsPhysicalDistanceToSeparatrix ≡ false
    twoBitRegressionMeasuresRealBioelectricCapacity : Bool
    twoBitRegressionMeasuresRealBioelectricCapacityIsFalse :
      twoBitRegressionMeasuresRealBioelectricCapacity ≡ false

canonicalBasinAuthorityBoundary : BasinAuthorityBoundary
canonicalBasinAuthorityBoundary = record
  { finiteDepthEqualsPhysicalDistanceToSeparatrix = false
  ; finiteDepthEqualsPhysicalDistanceToSeparatrixIsFalse = refl
  ; twoBitRegressionMeasuresRealBioelectricCapacity = false
  ; twoBitRegressionMeasuresRealBioelectricCapacityIsFalse = refl
  }
