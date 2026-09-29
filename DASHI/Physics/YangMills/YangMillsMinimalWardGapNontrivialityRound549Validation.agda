{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsMinimalWardGapNontrivialityRound549Validation where
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.YangMillsMinimalWardGapNontrivialityRound549Exact as R549
open import DASHI.Physics.YangMills.CompactLieProofLevel
compilerMachineChecked : R549.round549MinimalNontrivialityCompilerLevel ≡ machineChecked
compilerMachineChecked = refl
fullCNotRequiredForH6 : R549.fullOPEStressPackageRequiredForH6Contradiction ≡ false
fullCNotRequiredForH6 = refl
