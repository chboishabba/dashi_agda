{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsProjectiveCylinderMeasureRepresentationRound534Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsProjectiveCylinderMeasureRepresentationRound534Exact as R534
open import DASHI.Physics.YangMills.CompactLieProofLevel

projectiveCompilerMachineChecked :
  R534.round534ProjectiveRepresentationCompilerLevel ≡ machineChecked
projectiveCompilerMachineChecked = refl

wholeProjectiveRequired :
  R534.wholeProjectiveFamilyRequiredForPreferredExtension ≡ true
wholeProjectiveRequired = refl

singleCutoffNotPreferred :
  R534.selectedSingleCutoffExtensionIsPreferredContinuumRoute ≡ false
singleCutoffNotPreferred = refl
