{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsRepresentedContinuumCarrierRound450Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsRepresentedContinuumCarrierRound450Exact as R450
open import DASHI.Physics.YangMills.CompactLieProofLevel

representedCarrierCompilerMachineChecked :
  R450.round450RepresentedCarrierCompilerLevel ≡ machineChecked
representedCarrierCompilerMachineChecked = refl

expectationByIntegrationIsDefinitional :
  R450.round450ExpectationByIntegrationDefinitionalLevel ≡ machineChecked
expectationByIntegrationIsDefinitional = refl

schwingerSameCarrierIsDefinitional :
  R450.round450SchwingerSameCarrierDefinitionalLevel ≡ machineChecked
schwingerSameCarrierIsDefinitional = refl

countablyAdditiveRepresentationRemainsPhysical :
  R450.round450CountablyAdditiveRepresentationLevel ≡ conditional
countablyAdditiveRepresentationRemainsPhysical = refl
