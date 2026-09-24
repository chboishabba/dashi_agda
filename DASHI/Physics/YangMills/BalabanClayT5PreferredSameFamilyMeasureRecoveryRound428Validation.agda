{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5PreferredSameFamilyMeasureRecoveryRound428Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5PreferredSameFamilyMeasureRecoveryRound428Exact as R428
open import DASHI.Physics.YangMills.CompactLieProofLevel

preferredSameFamilyMeasureCompilerMachineChecked :
  R428.round428PreferredSameFamilyMeasureCompilerLevel ≡ machineChecked
preferredSameFamilyMeasureCompilerMachineChecked = refl

gramMeasureWeldCompilerMachineChecked :
  R428.round428GramMeasurePresentationWeldLevel ≡ machineChecked
gramMeasureWeldCompilerMachineChecked = refl

independentGramMeasurePaymentPruned :
  R428.round428IndependentGramMeasureSameObjectPaymentRequired ≡ false
independentGramMeasurePaymentPruned = refl
