{-# OPTIONS --safe #-}
module crisis.adversarial.BoundedSwitchingCriteriaValidation where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)

import crisis.adversarial.BoundedSwitchingCriteriaExact as Switch

------------------------------------------------------------------------
-- Deterministic validation for AO fleet leaf 0ff4fa16ae76.
------------------------------------------------------------------------

entryCriterionIsBounded :
  Switch.crisisEntryCriterion Switch.dualAdversarialSignal ≡ true
entryCriterionIsBounded =
  Switch.dualSignalEntersCrisis

returnCriterionRequiresNominalSupportAndClearSignals :
  Switch.nominalReturnCriterion
    Switch.canonicalNominalSupport
    Switch.clearSignal
  ≡ true
returnCriterionRequiresNominalSupportAndClearSignals =
  Switch.clearSignalPermitsNominalReturn

entryArmsTwoTickCooldown :
  Switch.step
    (Switch.controller-state Switch.macroscopicEigenMotif zero)
    Switch.canonicalNominalSupport
    Switch.dualAdversarialSignal
  ≡ Switch.controller-state Switch.crisisAdversarial Switch.twoTicks
entryArmsTwoTickCooldown =
  Switch.nominalToCrisisSwitch

returnArmsTwoTickCooldown :
  Switch.step
    (Switch.controller-state Switch.crisisAdversarial zero)
    Switch.canonicalNominalSupport
    Switch.clearSignal
  ≡ Switch.controller-state Switch.macroscopicEigenMotif Switch.twoTicks
returnArmsTwoTickCooldown =
  Switch.crisisToNominalSwitch

firstCooldownTickCannotBounce :
  Switch.step
    (Switch.step
      (Switch.controller-state Switch.macroscopicEigenMotif zero)
      Switch.canonicalNominalSupport
      Switch.dualAdversarialSignal)
    Switch.canonicalNominalSupport
    Switch.clearSignal
  ≡ Switch.controller-state Switch.crisisAdversarial (suc zero)
firstCooldownTickCannotBounce =
  Switch.immediateBounceBackIsBlocked

firstCooldownTickCannotReenter :
  Switch.step
    (Switch.step
      (Switch.controller-state Switch.crisisAdversarial zero)
      Switch.canonicalNominalSupport
      Switch.clearSignal)
    Switch.canonicalNominalSupport
    Switch.dualAdversarialSignal
  ≡ Switch.controller-state Switch.macroscopicEigenMotif (suc zero)
firstCooldownTickCannotReenter =
  Switch.immediateReentryIsBlocked

twoProtectedTicksExpireExactly :
  Switch.step
    (Switch.step
      (Switch.controller-state Switch.crisisAdversarial Switch.twoTicks)
      Switch.canonicalNominalSupport
      Switch.dualAdversarialSignal)
    Switch.canonicalNominalSupport
    Switch.clearSignal
  ≡ Switch.controller-state Switch.crisisAdversarial zero
twoProtectedTicksExpireExactly =
  Switch.twoCooldownTicksConsumeExactly
    Switch.crisisAdversarial
    Switch.canonicalNominalSupport
    Switch.canonicalNominalSupport
    Switch.dualAdversarialSignal
    Switch.clearSignal
