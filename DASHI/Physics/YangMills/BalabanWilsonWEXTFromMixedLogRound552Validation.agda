{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanWilsonWEXTFromMixedLogRound552Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanWilsonWEXTFromMixedLogRound552Exact as R552
open import DASHI.Physics.YangMills.CompactLieProofLevel

adapterMachineChecked :
  R552.round552WEXTAdapterCompilerLevel ≡ machineChecked
adapterMachineChecked = refl

independentCovarianceFieldPruned :
  R552.round552IndependentCovarianceExpansionFieldRequired ≡ false
independentCovarianceFieldPruned = refl
