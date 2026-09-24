{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPreferredTheoremFamilyCutRound531Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayPreferredTheoremFamilyCutRound531Exact as R531
open import DASHI.Physics.YangMills.CompactLieProofLevel

preferredFamilyCountIsSixteen :
  R531.preferredTheoremFamilyCount ≡ 16
preferredFamilyCountIsSixteen = refl

logicalSubclaimsRemainVisible :
  R531.allLogicalSubclaimsRemainVisible ≡ true
logicalSubclaimsRemainVisible = refl

groupingDoesNotDischargeSubclaims :
  R531.familyGroupingDischargesSubclaimsByItself ≡ false
groupingDoesNotDischargeSubclaims = refl

noOpaqueEndpointPredicates :
  R531.opaqueEndpointPredicatesInPreferredRoute ≡ false
noOpaqueEndpointPredicates = refl

noConstructorChoiceEqualities :
  R531.constructorChoiceEqualitiesInPreferredRoute ≡ false
noConstructorChoiceEqualities = refl

preferredFamilyCutCompilerMachineChecked :
  R531.round531PreferredTheoremFamilyCutCompilerLevel ≡ machineChecked
preferredFamilyCutCompilerMachineChecked = refl
