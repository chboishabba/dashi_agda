{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsFixedGroupProblemRound451Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsFixedGroupProblemRound451Exact as R451
open import DASHI.Physics.YangMills.CompactLieProofLevel

fixedGroupCompilerMachineChecked :
  R451.round451FixedGroupSpecializationCompilerLevel ≡ machineChecked
fixedGroupCompilerMachineChecked = refl

postHocSameGroupEqualityPruned :
  R451.round451PostHocSameGroupEqualityRequired ≡ false
postHocSameGroupEqualityPruned = refl

noUniformAcrossGroupsConstantIntroduced :
  R451.round451UniformAcrossGroupsConstantRequiredBySpecialization ≡ false
noUniformAcrossGroupsConstantIntroduced = refl
