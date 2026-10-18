{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5BoundedWeakPreGapCoreRound440Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5BoundedWeakPreGapCoreRound440Exact as R440
open import DASHI.Physics.YangMills.CompactLieProofLevel

preGapCoreCompilerMachineChecked :
  R440.round440PreGapCoreCompilerLevel ≡ machineChecked
preGapCoreCompilerMachineChecked = refl

fullSelectedMeasureConvergenceMachineChecked :
  R440.round440FullSelectedMeasureConvergenceLevel ≡ machineChecked
fullSelectedMeasureConvergenceMachineChecked = refl

legacyTotalLimitPruned :
  R440.round440LegacyTotalSequentialLimitRequired ≡ false
legacyTotalLimitPruned = refl

clusteringNotRequiredForCore :
  R440.round440ClusteringRequiredForPreGapCore ≡ false
clusteringNotRequiredForCore = refl

independentMeasureContinuityPruned :
  R440.round440IndependentMeasureContinuityTheoremRequired ≡ false
independentMeasureContinuityPruned = refl
