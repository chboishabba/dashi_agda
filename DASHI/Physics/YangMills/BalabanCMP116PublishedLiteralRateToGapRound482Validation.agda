{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116PublishedLiteralRateToGapRound482Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanCMP116PublishedLiteralRateToGapRound482Exact as R482
open import DASHI.Physics.YangMills.CompactLieProofLevel

compilerMachineChecked :
  R482.round482RateToGapCompilerLevel ≡ machineChecked
compilerMachineChecked = refl

positiveGapTokenPruned :
  R482.arbitraryPositiveCandidateGapTokenRequired ≡ false
positiveGapTokenPruned = refl

globalInversePruned :
  R482.globalEnergyToDecayInverseRequired ≡ false
globalInversePruned = refl
