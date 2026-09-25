{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCriticalPathRound555Validation where
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.YangMillsClayCriticalPathRound555Exact as R555
open import DASHI.Physics.YangMills.CompactLieProofLevel
criticalCountIsEight : R555.criticalFamilyCount ≡ 8
criticalCountIsEight = refl
gapCompilerMachineChecked : R555.massGapCompilerLevel ≡ machineChecked
gapCompilerMachineChecked = refl
h6CompilerMachineChecked : R555.minimalH6CompilerLevel ≡ machineChecked
h6CompilerMachineChecked = refl
fullCNotOnGapCut : R555.fullCLayerRequiredForMassGapCompiler ≡ false
fullCNotOnGapCut = refl
fullCNotOnH6Cut : R555.fullCLayerRequiredForMinimalH6Contradiction ≡ false
fullCNotOnH6Cut = refl
fullCRetainedForClay : R555.fullCLayerRetainedForConservativeClayLocalFieldExistence ≡ true
fullCRetainedForClay = refl
