{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5SelectedDiagonalTightnessRound431Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5SelectedDiagonalTightnessRound431Exact as R431
open import DASHI.Physics.YangMills.CompactLieProofLevel

subsequenceTightnessCompilerMachineChecked :
  R431.round431SubsequenceTightnessCompilerLevel ≡ machineChecked
subsequenceTightnessCompilerMachineChecked = refl

everySubsequenceTightInputPruned :
  R431.round431IndependentEverySubsequenceTightInputRequired ≡ false
everySubsequenceTightInputPruned = refl
