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
