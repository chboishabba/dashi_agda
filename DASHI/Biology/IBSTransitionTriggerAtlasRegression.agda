module DASHI.Biology.IBSTransitionTriggerAtlasRegression where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.IBSTransitionTriggerAtlasExact as Trigger

triggerAtlasRegression :
  Trigger.canonicalIBSTransitionTriggerAtlas ≡ Trigger.canonicalIBSTransitionTriggerAtlas
triggerAtlasRegression = refl

naturalTriggerNotMechanismRegression :
  Trigger.NaturalTriggerIdentifiesUniqueMechanismPermission → ⊥
naturalTriggerNotMechanismRegression = Trigger.naturalTriggerDoesNotIdentifyUniqueMechanism

wearableNotStateRegression :
  Trigger.WearableProxyIdentifiesLatentStatePermission → ⊥
wearableNotStateRegression = Trigger.wearableProxyDoesNotIdentifyLatentState

postInfectiousNotAttractorRegression :
  Trigger.PostInfectiousPersistenceValidatesAttractorPermission → ⊥
postInfectiousNotAttractorRegression = Trigger.postInfectiousPersistenceDoesNotValidateAttractor

triggerFrontierRegression :
  Trigger.canonicalTransitionTriggerParetoFrontier ≡ Trigger.canonicalTransitionTriggerParetoFrontier
triggerFrontierRegression = refl
