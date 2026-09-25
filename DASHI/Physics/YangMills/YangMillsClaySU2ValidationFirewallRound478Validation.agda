{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClaySU2ValidationFirewallRound478Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClaySU2ValidationFirewallRound478Exact as R478
open import DASHI.Physics.YangMills.CompactLieProofLevel

su2NotGenericPremise :
  R478.su2ValidationRequiredForGenericConstruction ≡ false
su2NotGenericPremise = refl

genericMayValidateAtSU2 :
  R478.genericConstructionMayBeValidatedAtSU2 ≡ true
genericMayValidateAtSU2 = refl

singleGroupDoesNotPromote :
  R478.singleGroupValidationPromotesToAllCompactSimpleGroups ≡ false
singleGroupDoesNotPromote = refl

compilerMachineChecked :
  R478.round478ValidationFirewallCompilerLevel ≡ machineChecked
compilerMachineChecked = refl
