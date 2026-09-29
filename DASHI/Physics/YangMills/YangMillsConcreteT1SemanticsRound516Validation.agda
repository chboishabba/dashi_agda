{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsConcreteT1SemanticsRound516Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsConcreteT1SemanticsRound516Exact as R516
open import DASHI.Physics.YangMills.CompactLieProofLevel

t1SemanticsCompilerMachineChecked :
  R516.round516ConcreteT1SemanticsCompilerLevel ≡ machineChecked
t1SemanticsCompilerMachineChecked = refl

finiteNormalizationCompilerMachineChecked :
  R516.round516FiniteNormalizationCompilerLevel ≡ machineChecked
finiteNormalizationCompilerMachineChecked = refl

publishedRPCompilerMachineChecked :
  R516.round516PublishedFiniteRPCompilerLevel ≡ machineChecked
publishedRPCompilerMachineChecked = refl

cutoffCompatibilityCompilerMachineChecked :
  R516.round516ProjectiveCutoffCompatibilityCompilerLevel ≡ machineChecked
cutoffCompatibilityCompilerMachineChecked = refl

t1SourceBundleRemainsPhysical :
  R516.literalRound516ConcreteT1SourceBundleLevel ≡ conditional
t1SourceBundleRemainsPhysical = refl
