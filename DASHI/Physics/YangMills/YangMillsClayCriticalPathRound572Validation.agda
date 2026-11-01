{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCriticalPathRound572Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayCriticalPathRound572Exact as R572
open import DASHI.Physics.YangMills.CompactLieProofLevel

criticalFamilyCountIsSeven :
  R572.criticalFamilyCount ≡ 7
criticalFamilyCountIsSeven = refl

g1AlignmentCompilerOwned :
  R572.g1AlignmentCompilerLevel ≡ machineChecked
g1AlignmentCompilerOwned = refl

criticalPathCompilerMachineChecked :
  R572.round572CriticalPathCompilerLevel ≡ machineChecked
criticalPathCompilerMachineChecked = refl
