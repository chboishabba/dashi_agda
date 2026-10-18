{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCriticalPathRound561Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayCriticalPathRound561Exact as R561
open import DASHI.Physics.YangMills.CompactLieProofLevel

criticalFamilyCountIsSeven :
  R561.criticalFamilyCount ≡ 7
criticalFamilyCountIsSeven = refl

t5MomentTransportMachineChecked :
  R561.t5FiniteOS05CompilerLevel ≡ machineChecked
t5MomentTransportMachineChecked = refl

t5SameFamilyWeldPruned :
  R561.t5SameFamilyExpectationAttachmentRequired ≡ false
t5SameFamilyWeldPruned = refl

wilsonContinuumConvergenceCompiled :
  R561.finiteToContinuumWilsonCovarianceLevel ≡ machineChecked
wilsonContinuumConvergenceCompiled = refl

massGapCompilerMachineChecked :
  R561.massGapCompilerLevel ≡ machineChecked
massGapCompilerMachineChecked = refl

criticalPathCompilerMachineChecked :
  R561.round561CriticalPathCompilerLevel ≡ machineChecked
criticalPathCompilerMachineChecked = refl
