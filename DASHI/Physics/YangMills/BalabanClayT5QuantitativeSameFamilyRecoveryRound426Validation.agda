{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5QuantitativeSameFamilyRecoveryRound426Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5QuantitativeSameFamilyRecoveryRound426Exact as R426
open import DASHI.Physics.YangMills.CompactLieProofLevel

selectedClosureCompilerMachineChecked :
  R426.round426SelectedClosureCompilerLevel ≡ machineChecked
selectedClosureCompilerMachineChecked = refl

sameFamilyRecoveryCompilerMachineChecked :
  R426.round426SameFamilyRecoveryCompilerLevel ≡ machineChecked
sameFamilyRecoveryCompilerMachineChecked = refl

separateP2AndOSMeasurePruned :
  R426.round426SeparateContinuumMeasureForP2AndOSRequired ≡ false
separateP2AndOSMeasurePruned = refl
