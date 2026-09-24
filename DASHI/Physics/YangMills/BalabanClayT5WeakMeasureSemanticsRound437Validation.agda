{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5WeakMeasureSemanticsRound437Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5WeakMeasureSemanticsRound437Exact as R437
open import DASHI.Physics.YangMills.CompactLieProofLevel

weakMeasurePropertyCompilerMachineChecked :
  R437.round437WeakMeasurePropertyCompilerLevel ≡ machineChecked
weakMeasurePropertyCompilerMachineChecked = refl

independentMeasurePropertyClosuresPruned :
  R437.round437IndependentMeasurePropertyClosureTheoremsRequired ≡ false
independentMeasurePropertyClosuresPruned = refl


preGapContinuumCoreCompilerMachineChecked :
  R437.round437PreGapContinuumCoreCompilerLevel ≡ machineChecked
preGapContinuumCoreCompilerMachineChecked = refl

fullMeasureConvergenceCompilerMachineChecked :
  R437.round437FullMeasureConvergenceLevel ≡ machineChecked
fullMeasureConvergenceCompilerMachineChecked = refl

clusteringNotRequiredForPreGapCore :
  R437.round437ClusteringRequiredForPreGapCore ≡ false
clusteringNotRequiredForPreGapCore = refl
