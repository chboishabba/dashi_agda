{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCriticalPathRound564Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayCriticalPathRound564Exact as R564
open import DASHI.Physics.YangMills.CompactLieProofLevel

criticalFamilyCountIsSeven :
  R564.criticalFamilyCount ≡ 7
criticalFamilyCountIsSeven = refl

wardAdapterMachineChecked :
  R564.h6WardAdapterLevel ≡ machineChecked
wardAdapterMachineChecked = refl

opeCoefficientOffCriticalPath :
  R564.h6OPECoefficientRequired ≡ false
opeCoefficientOffCriticalPath = refl

stressOffCriticalPath :
  R564.h6StressTensorRequired ≡ false
stressOffCriticalPath = refl

fullCStillRetainedForConservativeExistence :
  R564.fullCLayerRetainedForConservativeClayExistence ≡ true
fullCStillRetainedForConservativeExistence = refl

criticalPathCompilerMachineChecked :
  R564.round564CriticalPathCompilerLevel ≡ machineChecked
criticalPathCompilerMachineChecked = refl
