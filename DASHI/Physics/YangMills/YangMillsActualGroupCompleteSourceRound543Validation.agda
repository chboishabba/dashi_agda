{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsActualGroupCompleteSourceRound543Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsActualGroupCompleteSourceRound543Exact as R543
open import DASHI.Physics.YangMills.CompactLieProofLevel

compilerMachineChecked :
  R543.round543ActualGroupCompleteSourceCompilerLevel ≡ machineChecked
compilerMachineChecked = refl

noIndependentGroupSelection :
  R543.round543IndependentStructuralAndQuantitativeSelectionsAllowed ≡ false
noIndependentGroupSelection = refl

noSU2Promotion :
  R543.round543SU2PromotionAllowed ≡ false
noSU2Promotion = refl
