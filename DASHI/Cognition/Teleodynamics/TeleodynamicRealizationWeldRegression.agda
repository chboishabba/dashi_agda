module DASHI.Cognition.Teleodynamics.TeleodynamicRealizationWeldRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.Teleodynamics.TeleodynamicRealizationWeldExact as Weld

semanticEquivarianceDoesNotCreateRealization :
  Weld.semanticActionEquivarianceCreatesTargetRealization Weld.canonicalRealizationWeldBoundary ≡ false
semanticEquivarianceDoesNotCreateRealization = refl

explicitRealizationWitnessRequired :
  Weld.targetRealizationRequiresCommutingWitness Weld.canonicalRealizationWeldBoundary ≡ true
explicitRealizationWitnessRequired = refl

realizationStillDoesNotCreatePhenomenology :
  Weld.targetRealizationCreatesPhenomenalIdentity Weld.canonicalRealizationWeldBoundary ≡ false
realizationStillDoesNotCreatePhenomenology = refl

realizationStillDoesNotCreateAuthority :
  Weld.targetRealizationCreatesNormativeAuthority Weld.canonicalRealizationWeldBoundary ≡ false
realizationStillDoesNotCreateAuthority = refl
