{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPerGroupQuantifierScopeRound449Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayPerGroupQuantifierScopeRound449Exact as R449
open import DASHI.Physics.YangMills.CompactLieProofLevel

clayEndpointPointwiseInGroup :
  R449.clayEndpointIsPointwiseInCompactSimpleGroup ≡ true
clayEndpointPointwiseInGroup = refl

noGlobalUniformConstantDemand :
  R449.clayEndpointDemandsOneConstantUniformAcrossAllGroups ≡ false
noGlobalUniformConstantDemand = refl

groupDependentConstantsAllowed :
  R449.groupDependentAnalyticConstantsAreAllowedWhenConsumersArePerGroup ≡ true
groupDependentConstantsAllowed = refl

fixedGroupCutoffUniformityStillMatters :
  R449.cutoffUniformityWithinFixedGroupMayStillBeRequired ≡ true
fixedGroupCutoffUniformityStillMatters = refl

pointwiseDoesNotPromoteToUniform :
  R449.perGroupPaymentImpliesUniformAcrossGroupsPayment ≡ false
pointwiseDoesNotPromoteToUniform = refl

quantifierFirewallMachineChecked :
  R449.round449QuantifierFirewallLevel ≡ machineChecked
quantifierFirewallMachineChecked = refl
