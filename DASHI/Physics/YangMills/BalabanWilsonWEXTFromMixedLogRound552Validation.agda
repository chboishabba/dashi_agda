{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanWilsonWEXTFromMixedLogRound552Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanWilsonWEXTFromMixedLogRound552Exact as R552
open import DASHI.Physics.YangMills.CompactLieProofLevel

adapterMachineChecked :
  R552.wextAdapterCompilerLevel ≡ machineChecked
adapterMachineChecked = refl

independentCovarianceFieldPruned :
  R552.independentCovarianceExpansionFieldRequired ≡ false
independentCovarianceFieldPruned = refl
