{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5MarkedMomentProducerRound444Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5MarkedMomentProducerRound444Exact as R444
open import DASHI.Physics.YangMills.CompactLieProofLevel

markedMomentCompilerMachineChecked :
  R444.round444MarkedMomentToT5CompilerLevel ≡ machineChecked
markedMomentCompilerMachineChecked = refl

secondMomentTheoremPruned :
  R444.round444IndependentSecondExponentialMomentTheoremRequired ≡ false
secondMomentTheoremPruned = refl
