{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5SameFamilyContinuumRecoveryRound425Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5SameFamilyContinuumRecoveryRound425Exact as R425
open import DASHI.Physics.YangMills.CompactLieProofLevel

sameFamilyContinuumRecoveryCompilerMachineChecked :
  R425.round425SameFamilyContinuumRecoveryCompilerLevel ≡ machineChecked
sameFamilyContinuumRecoveryCompilerMachineChecked = refl

separateP2ContinuumMeasurePruned :
  R425.round425SeparateP2ContinuumMeasureRequired ≡ false
separateP2ContinuumMeasurePruned = refl

independentOSFamilyForP3Pruned :
  R425.round425IndependentOSFamilyForP3Required ≡ false
independentOSFamilyForP3Pruned = refl
