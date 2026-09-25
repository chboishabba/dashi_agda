{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCriticalPathRound558Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayCriticalPathRound558Exact as R558
open import DASHI.Physics.YangMills.CompactLieProofLevel

criticalFamilyCountIsSeven :
  R558.criticalFamilyCount ≡ 7
criticalFamilyCountIsSeven = refl

finiteToContinuumWilsonCovarianceIsCompiled :
  R558.finiteToContinuumWilsonCovarianceLevel ≡ machineChecked
finiteToContinuumWilsonCovarianceIsCompiled = refl

separateWilsonConvergenceFamilyPruned :
  R558.separateContinuumWilsonConvergenceFamilyRequired ≡ false
separateWilsonConvergenceFamilyPruned = refl

fullCNotMassGapPremise :
  R558.fullCLayerRequiredForMassGap ≡ false
fullCNotMassGapPremise = refl

fullCRetainedForClayExistence :
  R558.fullCLayerRetainedForConservativeClayExistence ≡ true
fullCRetainedForClayExistence = refl

criticalPathCompilerMachineChecked :
  R558.round558CriticalPathCompilerLevel ≡ machineChecked
criticalPathCompilerMachineChecked = refl
