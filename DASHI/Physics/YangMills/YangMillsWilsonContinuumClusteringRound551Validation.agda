{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsWilsonContinuumClusteringRound551Validation where
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.YangMillsWilsonContinuumClusteringRound551Exact as R551
open import DASHI.Physics.YangMills.CompactLieProofLevel
finiteCompilerMachineChecked : R551.round551FiniteWEXTToHalfRateCompilerLevel ≡ machineChecked
finiteCompilerMachineChecked = refl
orderClosureMachineChecked : R551.round551ContinuumOrderClosureCompilerLevel ≡ machineChecked
orderClosureMachineChecked = refl
printedJNotRequired : R551.printedJPresentationRequired ≡ false
printedJNotRequired = refl
