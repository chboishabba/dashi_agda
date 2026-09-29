{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5BoundedWeakCompactnessRound439Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5BoundedWeakCompactnessRound439Exact as R439
open import DASHI.Physics.YangMills.CompactLieProofLevel

selectedCompactnessCompilerMachineChecked :
  R439.round439SelectedCompactnessCompilerLevel ≡ machineChecked
selectedCompactnessCompilerMachineChecked = refl

fullSelectedMeasureConvergenceMachineChecked :
  R439.round439FullSelectedMeasureConvergenceLevel ≡ machineChecked
fullSelectedMeasureConvergenceMachineChecked = refl

legacyTotalLimitPruned :
  R439.round439LegacyTotalSequentialLimitRequired ≡ false
legacyTotalLimitPruned = refl

independentClusterUniquenessPruned :
  R439.round439IndependentClusterUniquenessTheoremRequired ≡ false
independentClusterUniquenessPruned = refl
