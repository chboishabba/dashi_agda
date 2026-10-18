{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayMinimalH6NontrivialityRound550Validation where
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.YangMillsClayMinimalH6NontrivialityRound550Exact as R550
open import DASHI.Physics.YangMills.CompactLieProofLevel
compilerMachineChecked : R550.round550MinimalH6CompilerLevel ≡ machineChecked
compilerMachineChecked = refl
fullCRecordNotRequired : R550.round550FullLocalOPEStressRecordRequiredForNontriviality ≡ false
fullCRecordNotRequired = refl
