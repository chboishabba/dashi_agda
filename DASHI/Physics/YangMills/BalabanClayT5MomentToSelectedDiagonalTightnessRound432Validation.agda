{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5MomentToSelectedDiagonalTightnessRound432Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5MomentToSelectedDiagonalTightnessRound432Exact as R432
open import DASHI.Physics.YangMills.CompactLieProofLevel

momentToDiagonalTightnessCompilerMachineChecked :
  R432.round432MomentToDiagonalTightnessCompilerLevel ≡ machineChecked
momentToDiagonalTightnessCompilerMachineChecked = refl

independentDiagonalTightnessPruned :
  R432.round432IndependentSelectedDiagonalTightnessTheoremRequired ≡ false
independentDiagonalTightnessPruned = refl
