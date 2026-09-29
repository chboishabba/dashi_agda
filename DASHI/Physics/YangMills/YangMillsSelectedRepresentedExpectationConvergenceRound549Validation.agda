{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSelectedRepresentedExpectationConvergenceRound549Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsSelectedRepresentedExpectationConvergenceRound549Exact as R549
open import DASHI.Physics.YangMills.CompactLieProofLevel

selectedConvergenceCompilerMachineChecked :
  R549.round549SelectedRepresentedConvergenceCompilerLevel ≡ machineChecked
selectedConvergenceCompilerMachineChecked = refl

arbitraryObservableRepresentationNotRequired :
  R549.round549ArbitraryObservableRepresentationRequired ≡ false
arbitraryObservableRepresentationNotRequired = refl

oldR499DependencyRemoved :
  R549.round549R499DependencyRequired ≡ false
oldR499DependencyRemoved = refl
