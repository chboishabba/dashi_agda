{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ContinuumSemanticCoreRound442Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ContinuumSemanticCoreRound442Exact as R442
open import DASHI.Physics.YangMills.CompactLieProofLevel

semanticCoreCompilerMachineChecked :
  R442.round442ConcreteContinuumSemanticCoreCompilerLevel ≡ machineChecked
semanticCoreCompilerMachineChecked = refl

independentContinuumWitnessPruned :
  R442.round442IndependentContinuumLimitWitnessRequired ≡ false
independentContinuumWitnessPruned = refl

independentSchwingerWitnessPruned :
  R442.round442IndependentSchwingerBelongingWitnessRequired ≡ false
independentSchwingerWitnessPruned = refl
