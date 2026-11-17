module DASHI.Physics.Foundations.PrecisionThrustClosureValidation where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.PrecisionThrustClosureExact as Precision

closureObligationExists : Precision.PrecisionThrustClosureObligation
closureObligationExists = Precision.canonicalPrecisionThrustClosureObligation

allNuisanceChannelsClosedStillOpen :
  Precision.allDeclaredNuisanceChannelsClosed
    Precision.canonicalPrecisionThrustClosureObligation
    ≡ false
allNuisanceChannelsClosedStillOpen = refl

independentReplicationStillOpen :
  Precision.independentReplicationPaid
    Precision.canonicalPrecisionThrustClosureObligation
    ≡ false
independentReplicationStillOpen = refl

gravityInterpretationStillOpen :
  Precision.independentGravityConsumerPaid
    Precision.canonicalPrecisionThrustClosureObligation
    ≡ false
gravityInterpretationStillOpen = refl

residualAloneDoesNotCloseNuisance : Bool
residualAloneDoesNotCloseNuisance =
  Precision.residualMagnitudeDoesNotCloseNuisance
    Precision.canonicalPrecisionThrustBoundary
