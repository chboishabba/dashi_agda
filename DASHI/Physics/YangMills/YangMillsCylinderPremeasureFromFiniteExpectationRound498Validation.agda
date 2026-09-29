{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsCylinderPremeasureFromFiniteExpectationRound498Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsCylinderPremeasureFromFiniteExpectationRound498Exact as R498
open import DASHI.Physics.YangMills.CompactLieProofLevel

finitePremeasureCompilerMachineChecked :
  R498.round498FinitePremeasureCompilerLevel ≡ machineChecked
finitePremeasureCompilerMachineChecked = refl

projectivePremeasureCompilerMachineChecked :
  R498.round498ProjectivePremeasureCompilerLevel ≡ machineChecked
projectivePremeasureCompilerMachineChecked = refl
