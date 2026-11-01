{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayT5CoerciveQuantitativeMaxCutRound447Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayT5CoerciveQuantitativeMaxCutRound447Exact as R447
open import DASHI.Physics.YangMills.CompactLieProofLevel

quantitativeMaxCutCompilerMachineChecked :
  R447.round447QuantitativeMaxCutCompilerLevel ≡ machineChecked
quantitativeMaxCutCompilerMachineChecked = refl

independentTightnessPruned :
  R447.round447IndependentTightnessTheoremRequired ≡ false
independentTightnessPruned = refl
