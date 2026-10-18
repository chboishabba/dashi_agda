{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5Path4ToSelectedDiagonalTightnessRound433Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5Path4ToSelectedDiagonalTightnessRound433Exact as R433
open import DASHI.Physics.YangMills.CompactLieProofLevel

path4ToDiagonalTightnessCompilerMachineChecked :
  R433.round433Path4ToDiagonalTightnessCompilerLevel ≡ machineChecked
path4ToDiagonalTightnessCompilerMachineChecked = refl

pointwiseCoercivityCompilerMachineChecked :
  R433.round433PointwiseCoercivityLevel ≡ machineChecked
pointwiseCoercivityCompilerMachineChecked = refl

independentTightnessTheoremPruned :
  R433.round433IndependentTightnessTheoremRequired ≡ false
independentTightnessTheoremPruned = refl
