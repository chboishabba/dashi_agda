{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPostSelectedCylinderFrontierRound548Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayPostSelectedCylinderFrontierRound548Exact as R548
open import DASHI.Physics.YangMills.CompactLieProofLevel

familyCountStillFourteen :
  R548.preferredSourceFamilyCount ≡ 14
familyCountStillFourteen = refl

generatorRepresentationMachineChecked :
  R548.a3CylinderGeneratorRepresentationLevel ≡ machineChecked
generatorRepresentationMachineChecked = refl

arbitraryObservableRepresentationNotRequired :
  R548.arbitraryConfigurationObservableRepresentationRequired ≡ false
arbitraryObservableRepresentationNotRequired = refl

selectedClosureStillPhysical :
  R548.selectedObservableClosureStillPhysical ≡ true
selectedClosureStillPhysical = refl

compilerMachineChecked :
  R548.round548PostSelectedCylinderFrontierCompilerLevel ≡ machineChecked
compilerMachineChecked = refl
