{-# OPTIONS --safe #-}
module crisis.adversarial.BoundedSwitchingCriteriaExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

------------------------------------------------------------------------
-- AO fleet leaf 0ff4fa16ae76.
--
-- This module is deliberately local to crisis/adversarial typed support.
-- It adds a bounded switching controller between:
--
--   * crisis/adversarial mode; and
--   * the macroscopic eigen-motif whose retained support is the three
--     NominalModifier properties named by the fleet obligation.
--
-- The controller is structural only.
-- It does not infer crisis from repository identity.
-- It does not promote a spectral motif into semantic truth.
-- It does not create authority from a PNF property label.
------------------------------------------------------------------------

data FleetMode : Set where
  macroscopicEigenMotif : FleetMode
  crisisAdversarial : FleetMode

record MacroscopicEigenMotifSupport : Set where
  constructor eigen-motif-support
  field
    propertyChboishabbaNominalModifier : Bool
    propertyReposNominalModifier : Bool
    propertyDashiAgdaNominalModifier : Bool

open MacroscopicEigenMotifSupport public

record CrisisAdversarialSignal : Set where
  constructor crisis-signal
  field
    integrityFailure : Bool
    provenanceConflict : Bool
    adversarialInput : Bool

open CrisisAdversarialSignal public

------------------------------------------------------------------------
-- Boolean criteria.
------------------------------------------------------------------------

_&&_ : Bool → Bool → Bool
true && b = b
false && b = false

atLeastTwo : Bool → Bool → Bool → Bool
atLeastTwo true true c = true
atLeastTwo true false true = true
atLeastTwo false true true = true
atLeastTwo _ _ _ = false

allNominalModifiers : MacroscopicEigenMotifSupport → Bool
allNominalModifiers support =
  propertyChboishabbaNominalModifier support
  && propertyReposNominalModifier support
  && propertyDashiAgdaNominalModifier support

crisisEntryCriterion : CrisisAdversarialSignal → Bool
crisisEntryCriterion signal =
  atLeastTwo
    (integrityFailure signal)
    (provenanceConflict signal)
    (adversarialInput signal)

allCrisisSignalsClear : CrisisAdversarialSignal → Bool
allCrisisSignalsClear (crisis-signal false false false) = true
allCrisisSignalsClear _ = false

nominalReturnCriterion :
  MacroscopicEigenMotifSupport →
  CrisisAdversarialSignal →
  Bool
nominalReturnCriterion support signal =
  allNominalModifiers support && allCrisisSignalsClear signal

------------------------------------------------------------------------
-- Bounded anti-chatter controller.
--
-- A switch arms a two-tick cooldown.
-- While cooldown is positive, no mode transition can occur.
-- Therefore two complete controller ticks separate a completed switch from
-- the next tick that is permitted to evaluate a switch criterion.
------------------------------------------------------------------------

twoTicks : Nat
twoTicks = suc (suc zero)

record ControllerState : Set where
  constructor controller-state
  field
    mode : FleetMode
    cooldown : Nat

open ControllerState public

step :
  ControllerState →
  MacroscopicEigenMotifSupport →
  CrisisAdversarialSignal →
  ControllerState
step (controller-state current (suc remaining)) support signal =
  controller-state current remaining
step (controller-state macroscopicEigenMotif zero) support signal
  with crisisEntryCriterion signal
... | true = controller-state crisisAdversarial twoTicks
... | false = controller-state macroscopicEigenMotif zero
step (controller-state crisisAdversarial zero) support signal
  with nominalReturnCriterion support signal
... | true = controller-state macroscopicEigenMotif twoTicks
... | false = controller-state crisisAdversarial zero

------------------------------------------------------------------------
-- Exact bounded-switching theorems.
------------------------------------------------------------------------

cooldownBlocksSwitching :
  (current : FleetMode) →
  (remaining : Nat) →
  (support : MacroscopicEigenMotifSupport) →
  (signal : CrisisAdversarialSignal) →
  step
    (controller-state current (suc remaining))
    support
    signal
  ≡ controller-state current remaining
cooldownBlocksSwitching current remaining support signal = refl

twoCooldownTicksConsumeExactly :
  (current : FleetMode) →
  (support1 support2 : MacroscopicEigenMotifSupport) →
  (signal1 signal2 : CrisisAdversarialSignal) →
  step
    (step
      (controller-state current twoTicks)
      support1
      signal1)
    support2
    signal2
  ≡ controller-state current zero
twoCooldownTicksConsumeExactly current support1 support2 signal1 signal2 = refl

------------------------------------------------------------------------
-- Canonical finite fixtures for both directions.
------------------------------------------------------------------------

canonicalNominalSupport : MacroscopicEigenMotifSupport
canonicalNominalSupport =
  eigen-motif-support true true true

clearSignal : CrisisAdversarialSignal
clearSignal =
  crisis-signal false false false

dualAdversarialSignal : CrisisAdversarialSignal
dualAdversarialSignal =
  crisis-signal true true false

canonicalNominalSupportIsReady :
  allNominalModifiers canonicalNominalSupport ≡ true
canonicalNominalSupportIsReady = refl

dualSignalEntersCrisis :
  crisisEntryCriterion dualAdversarialSignal ≡ true
dualSignalEntersCrisis = refl

clearSignalPermitsNominalReturn :
  nominalReturnCriterion canonicalNominalSupport clearSignal ≡ true
clearSignalPermitsNominalReturn = refl

nominalToCrisisSwitch :
  step
    (controller-state macroscopicEigenMotif zero)
    canonicalNominalSupport
    dualAdversarialSignal
  ≡ controller-state crisisAdversarial twoTicks
nominalToCrisisSwitch = refl

crisisToNominalSwitch :
  step
    (controller-state crisisAdversarial zero)
    canonicalNominalSupport
    clearSignal
  ≡ controller-state macroscopicEigenMotif twoTicks
crisisToNominalSwitch = refl

immediateBounceBackIsBlocked :
  step
    (step
      (controller-state macroscopicEigenMotif zero)
      canonicalNominalSupport
      dualAdversarialSignal)
    canonicalNominalSupport
    clearSignal
  ≡ controller-state crisisAdversarial (suc zero)
immediateBounceBackIsBlocked = refl

immediateReentryIsBlocked :
  step
    (step
      (controller-state crisisAdversarial zero)
      canonicalNominalSupport
      clearSignal)
    canonicalNominalSupport
    dualAdversarialSignal
  ≡ controller-state macroscopicEigenMotif (suc zero)
immediateReentryIsBlocked = refl
