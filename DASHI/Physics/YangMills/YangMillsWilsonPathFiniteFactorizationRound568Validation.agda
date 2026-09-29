{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsWilsonPathFiniteFactorizationRound568Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsWilsonPathFiniteFactorizationRound568Exact as R568
open import DASHI.Physics.YangMills.CompactLieProofLevel

pathFactorizationMachineChecked :
  R568.round568WilsonPathFactorizationCompilerLevel ≡ machineChecked
pathFactorizationMachineChecked = refl

pathLocalityMachineChecked :
  R568.round568PathLocalityCompilerLevel ≡ machineChecked
pathLocalityMachineChecked = refl
