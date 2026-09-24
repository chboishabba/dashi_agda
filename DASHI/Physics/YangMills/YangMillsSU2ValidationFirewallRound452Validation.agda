{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSU2ValidationFirewallRound452Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsSU2ValidationFirewallRound452Exact as R452
open import DASHI.Physics.YangMills.CompactLieProofLevel

su2NotGenericPremise :
  R452.su2ExplicitValidationRequiredForGenericCompactSimpleConstruction ≡ false
su2NotGenericPremise = refl

genericMayInstantiateAtSU2 :
  R452.su2ValidationMayInstantiateGenericConstruction ≡ true
genericMayInstantiateAtSU2 = refl

singleGroupDoesNotPromoteToGeneric :
  R452.singleGroupValidationImpliesGenericCompactSimplePayment ≡ false
singleGroupDoesNotPromoteToGeneric = refl

validationFirewallMachineChecked :
  R452.round452ValidationPremiseFirewallLevel ≡ machineChecked
validationFirewallMachineChecked = refl
