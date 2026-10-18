{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5GlobalContainmentCompactnessRound434Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5GlobalContainmentCompactnessRound434Exact as R434
open import DASHI.Physics.YangMills.CompactLieProofLevel

globalContainmentCompactnessCompilerMachineChecked :
  R434.round434GlobalContainmentCompactnessCompilerLevel ≡ machineChecked
globalContainmentCompactnessCompilerMachineChecked = refl

selectedDiagonalTightnessCompilerMachineChecked :
  R434.round434SelectedDiagonalTightnessLevel ≡ machineChecked
selectedDiagonalTightnessCompilerMachineChecked = refl

independentTightnessTheoremPruned :
  R434.round434IndependentTightnessTheoremRequired ≡ false
independentTightnessTheoremPruned = refl
