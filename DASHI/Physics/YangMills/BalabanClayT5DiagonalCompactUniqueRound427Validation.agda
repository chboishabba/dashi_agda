{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5DiagonalCompactUniqueRound427Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5DiagonalCompactUniqueRound427Exact as R427
open import DASHI.Physics.YangMills.CompactLieProofLevel

diagonalCompactUniqueCompilerMachineChecked :
  R427.round427DiagonalCompactUniqueCompilerLevel ≡ machineChecked
diagonalCompactUniqueCompilerMachineChecked = refl

fullSequenceConvergenceInputPruned :
  R427.round427IndependentFullSequenceConvergenceInputRequired ≡ false
fullSequenceConvergenceInputPruned = refl
