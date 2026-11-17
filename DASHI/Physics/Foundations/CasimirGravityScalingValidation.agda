module DASHI.Physics.Foundations.CasimirGravityScalingValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CasimirGravityScalingReceiptExact as Scaling

brownMaclayScalingExecuted : Scaling.idealStressScalingExecutionPaid Scaling.canonicalCasimirGravityScalingBoundary ≡ true
brownMaclayScalingExecuted = refl

measuredGravityStillFalse : Scaling.measuredGravitationalBackreactionPaid Scaling.canonicalCasimirGravityScalingBoundary ≡ false
measuredGravityStillFalse = refl

warpStillFalse : Scaling.warpCapabilityPaid Scaling.canonicalCasimirGravityScalingBoundary ≡ false
warpStillFalse = refl
