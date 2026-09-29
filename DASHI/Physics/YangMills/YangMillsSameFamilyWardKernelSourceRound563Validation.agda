{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSameFamilyWardKernelSourceRound563Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsSameFamilyWardKernelSourceRound563Exact as R563
open import DASHI.Physics.YangMills.CompactLieProofLevel

adapterMachineChecked :
  R563.round563MinimalWardAdapterLevel ≡ machineChecked
adapterMachineChecked = refl

opeCoefficientNotRequired :
  R563.round563OPECoefficientRequiredForH6 ≡ false
opeCoefficientNotRequired = refl

opeRemainderNotRequired :
  R563.round563OPERemainderRequiredForH6 ≡ false
opeRemainderNotRequired = refl

stressNotRequired :
  R563.round563StressTensorRequiredForH6 ≡ false
stressNotRequired = refl
