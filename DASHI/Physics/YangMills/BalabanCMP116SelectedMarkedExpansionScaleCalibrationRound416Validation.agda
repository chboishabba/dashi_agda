{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionScaleCalibrationRound416Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionScaleCalibrationRound416Exact as R416
open import DASHI.Physics.YangMills.CompactLieProofLevel

r415ToBEnvCompilerIsMachineChecked :
  R416.round416R415ToBEnvCompilerLevel ≡ machineChecked
r415ToBEnvCompilerIsMachineChecked = refl

noSecondDecayInequality :
  R416.round416AdditionalDecayInequalityRequired ≡ false
noSecondDecayInequality = refl
