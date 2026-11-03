module DASHI.Cognition.Teleodynamics.TeleodynamicInteractionDynamicsRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.Teleodynamics.TeleodynamicInteractionDynamicsExact as Dyn

existingDynamicOwnerReused :
  Dyn.dynamicMultiQueryOwnerReused Dyn.canonicalInteractionDynamicsBoundary ≡ true
existingDynamicOwnerReused = refl

oneStepFitDoesNotProveTraceSafety :
  Dyn.oneStepFitImpliesArbitraryTraceSafety Dyn.canonicalInteractionDynamicsBoundary ≡ false
oneStepFitDoesNotProveTraceSafety = refl

interactionDoesNotCreateNonlocalChannel :
  Dyn.interactionDynamicsEstablishNonlocalTransmission Dyn.canonicalInteractionDynamicsBoundary ≡ false
interactionDoesNotCreateNonlocalChannel = refl
