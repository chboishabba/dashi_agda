{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayRepresentedA3Round480Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayRepresentedA3Round480Exact as R480
open import DASHI.Physics.YangMills.CompactLieProofLevel

compilerMachineChecked :
  R480.round480RepresentedA3CompilerLevel ≡ machineChecked
compilerMachineChecked = refl

noFunctionalPromotion :
  R480.postHocContinuumFunctionalToMeasurePromotionRequired ≡ false
noFunctionalPromotion = refl

noIndependentSchwingerChoice :
  R480.independentSchwingerCarrierChoiceRequired ≡ false
noIndependentSchwingerChoice = refl
