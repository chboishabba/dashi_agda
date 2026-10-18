{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R413ToR406RefinementRound422Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanCMP116R413ToR406RefinementRound422Exact as R422
open import DASHI.Physics.YangMills.CompactLieProofLevel

r413ToR406RefinementMachineChecked :
  R422.round422R413ToR406RefinementCompilerLevel ≡ machineChecked
r413ToR406RefinementMachineChecked = refl

independentR410ReplayPruned :
  R422.round422IndependentR410ReplayRequired ≡ false
independentR410ReplayPruned = refl
