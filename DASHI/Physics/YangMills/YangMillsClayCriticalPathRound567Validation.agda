{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCriticalPathRound567Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayCriticalPathRound567Exact as R567
open import DASHI.Physics.YangMills.CompactLieProofLevel

criticalFamilyCountIsSeven :
  R567.criticalFamilyCount ≡ 7
criticalFamilyCountIsSeven = refl

finiteSelectedConvergenceCompilerOwned :
  R567.a3FiniteToRepresentedConvergenceCompilerLevel ≡ machineChecked
finiteSelectedConvergenceCompilerOwned = refl

criticalPathCompilerMachineChecked :
  R567.round567CriticalPathCompilerLevel ≡ machineChecked
criticalPathCompilerMachineChecked = refl
