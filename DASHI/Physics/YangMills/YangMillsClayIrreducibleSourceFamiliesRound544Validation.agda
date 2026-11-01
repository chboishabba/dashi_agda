{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayIrreducibleSourceFamiliesRound544Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayIrreducibleSourceFamiliesRound544Exact as R544
open import DASHI.Physics.YangMills.CompactLieProofLevel

familyCountIsFourteen :
  R544.preferredSourceFamilyCount ≡ 14
familyCountIsFourteen = refl

noOpaqueEndpoints :
  R544.opaqueEndpointPredicatesRemaining ≡ false
noOpaqueEndpoints = refl

noConstructorEqualities :
  R544.constructorChoiceEqualitiesRemaining ≡ false
noConstructorEqualities = refl

noWholeMeasureEquality :
  R544.wholeMeasureRecordEqualitiesRemaining ≡ false
noWholeMeasureEquality = refl

noIndependentGroupSelections :
  R544.independentStructuralAndQuantitativeGroupSelectionsRemaining ≡ false
noIndependentGroupSelections = refl

frontierCompilerMachineChecked :
  R544.round544IrreducibleSourceFamilyCutCompilerLevel ≡ machineChecked
frontierCompilerMachineChecked = refl
