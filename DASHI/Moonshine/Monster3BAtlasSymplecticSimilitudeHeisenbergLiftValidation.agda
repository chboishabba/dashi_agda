module DASHI.Moonshine.Monster3BAtlasSymplecticSimilitudeHeisenbergLiftValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BAtlasSymplecticSimilitudeHeisenbergLiftExact as Lift

similitudeInterfacePaid :
  Lift.similitudeActionInterfacePaid Lift.canonicalBoundary ≡ true
similitudeInterfacePaid = refl

centerScalingExposed :
  Lift.centerMultiplierLiftExposed Lift.canonicalBoundary ≡ true
centerScalingExposed = refl

quadraticCorrectionConditionExposed :
  Lift.similitudeCocycleCorrectionConditionExposed Lift.canonicalBoundary ≡ true
quadraticCorrectionConditionExposed = refl

primitiveConcreteCorrectionRuntimePaid :
  Lift.preferredPrimitiveConcreteCorrectionRuntimePaid Lift.canonicalBoundary ≡ true
primitiveConcreteCorrectionRuntimePaid = refl

primitiveConcreteLiftKernelStillOpen :
  Lift.preferredPrimitiveConcreteLiftKernelPaid Lift.canonicalBoundary ≡ false
primitiveConcreteLiftKernelStillOpen = refl
