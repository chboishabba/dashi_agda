{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayFixedGroupMaxCutRound477Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayFixedGroupMaxCutRound477Exact as R477
open import DASHI.Physics.YangMills.CompactLieProofLevel

fixedGroupCompilerMachineChecked :
  R477.round477FixedGroupCompilerLevel ≡ machineChecked
fixedGroupCompilerMachineChecked = refl

externalQuantifier :
  R477.clayQuantifierIsExternalPerGroup ≡ true
externalQuantifier = refl

noAcrossGroupConstant :
  R477.oneConstantUniformAcrossAllGroupsRequired ≡ false
noAcrossGroupConstant = refl

groupConstantsAllowed :
  R477.groupDependentConstantsAllowed ≡ true
groupConstantsAllowed = refl

postHocGroupWeldPruned :
  R477.postHocSameGroupWeldRequired ≡ false
postHocGroupWeldPruned = refl
