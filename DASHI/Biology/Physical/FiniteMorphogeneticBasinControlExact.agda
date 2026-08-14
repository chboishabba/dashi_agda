module DASHI.Biology.Physical.FiniteMorphogeneticBasinControlExact where

------------------------------------------------------------------------
-- Finite quantitative upgrade of GoalErrorDescentControllerExact.
--
-- The purpose is to make basin membership, reachability, intervention cost,
-- robustness depth and target-channel capacity explicit before any empirical
-- continuous-state calibration is supplied.  It is not a claim that a real
-- organ has four discrete states or that real control energy is measured by
-- this Nat cost.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.GoalErrorDescentControllerExact as Descent

------------------------------------------------------------------------
-- Basin geometry.
------------------------------------------------------------------------

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

-- Number of certified passive steps to target in this finite regression.
robustnessDepth : BasinState → Nat
robustnessDepth target = 0
robustnessDepth near = 1
robustnessDepth far = 2
robustnessDepth failed = 3

nearMoreRobustThanFar : robustnessDepth near < robustnessDepth far
nearMoreRobustThanFar = s≤s z≤n

------------------------------------------------------------------------
-- Controlled reachability and exact minimal one-step intervention cost.
------------------------------------------------------------------------

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
oneStepTargetingCostsAtLeastTwo noControl ()
oneStepTargetingCostsAtLeastTwo mildPulse ()
oneStepTargetingCostsAtLeastTwo strongPulse p = ≤-refl

strongPulseIsOneStepCostOptimal :
  (u : Intervention) → OneStepTargeting u →
  controlCost strongPulse ≤ controlCost u
strongPulseIsOneStepCostOptimal = oneStepTargetingCostsAtLeastTwo

------------------------------------------------------------------------
-- Two mild actions cost the same as one strong action but traverse a distinct
-- path.  Endpoint competence therefore does not identify microscopic policy.
------------------------------------------------------------------------

controlledTwice : Intervention → BasinState → BasinState
controlledTwice u x = controlledStep u (controlledStep u x)

twoMildReachTarget : controlledTwice mildPulse far ≡ target
twoMildReachTarget = refl

sameNominalCostDifferentControlPath :
  controlCost strongPulse ≡ controlCost mildPulse + controlCost mildPulse
sameNominalCostDifferentControlPath = refl

------------------------------------------------------------------------
-- Target-channel capacity: four explicitly distinguishable target basins have
-- an exact two-bit fixed-width code.  This is a lower-level finite capacity
-- regression, complementary to the existing 3-bit/eight-target theorem.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Empirical calibration boundary.  Real basin geometry should eventually
-- replace these finite carriers with measured latent states, intervention
-- costs and success probabilities/committors.
------------------------------------------------------------------------

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
