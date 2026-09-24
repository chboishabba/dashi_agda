{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayMomentOS05MaxCutRound500Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayMomentOS05MaxCutRound500Exact as R500
open import DASHI.Physics.YangMills.CompactLieProofLevel

compilerMachineChecked :
  R500.round500OS05CompilerLevel ≡ machineChecked
compilerMachineChecked = refl
