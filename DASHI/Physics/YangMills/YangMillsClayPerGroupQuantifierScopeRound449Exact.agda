{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPerGroupQuantifierScopeRound449Exact where

------------------------------------------------------------------------
-- ROUND449 / PER-G VS UNIFORM-OVER-G QUANTIFIER FIREWALL
--
-- Clay requires the construction for every compact simple gauge group.
-- This is pointwise in G:
--
--   ∀ G,  payment G
--
-- It does NOT by itself require one analytic constant to serve every G:
--
--   ∃ c, ∀ G, payment G c.
--
-- Uniformity across cutoffs/scales INSIDE one fixed-G construction remains a
-- genuine requirement whenever a downstream theorem consumes it.  What is
-- rejected here is the accidental promotion from "for every G" to "one
-- constant uniform over the whole class of compact-simple G".
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Typed quantifier shapes.
------------------------------------------------------------------------

record PerGroupAnalyticPayment
    (Group : Set)
    (Claim : Group → Set) : Set₁ where
  field
    pay : ∀ group → Claim group

open PerGroupAnalyticPayment public

record UniformAcrossGroupsAnalyticPayment
    (Group Constant : Set)
    (Claim : Group → Constant → Set) : Set₁ where
  field
    commonConstant : Constant
    payUniformly : ∀ group → Claim group commonConstant

open UniformAcrossGroupsAnalyticPayment public

record GroupDependentConstantPayment
    (Group Constant : Set)
    (Claim : Group → Constant → Set) : Set₁ where
  field
    constantFor : Group → Constant
    payWithGroupConstant :
      ∀ group → Claim group (constantFor group)

open GroupDependentConstantPayment public

------------------------------------------------------------------------
-- Scope/provenance tags for YM analytic receipts.
------------------------------------------------------------------------

data YMAnalyticScope : Set where
  localChart : YMAnalyticScope
  globalConfiguration : YMAnalyticScope
  finiteCutoff : YMAnalyticScope
  cutoffUniform : YMAnalyticScope
  rationalSource : YMAnalyticScope
  realExpectation : YMAnalyticScope
  continuum : YMAnalyticScope
  perCompactSimpleGroup : YMAnalyticScope
  uniformAcrossCompactSimpleGroups : YMAnalyticScope

record ScopedEvidence (Claim : Set) : Set where
  constructor scoped
  field
    scope : YMAnalyticScope
    evidence : Claim

open ScopedEvidence public

------------------------------------------------------------------------
-- Audit receipts.
------------------------------------------------------------------------

clayEndpointIsPointwiseInCompactSimpleGroup : Bool
clayEndpointIsPointwiseInCompactSimpleGroup = true

clayEndpointDemandsOneConstantUniformAcrossAllGroups : Bool
clayEndpointDemandsOneConstantUniformAcrossAllGroups = false

groupDependentAnalyticConstantsAreAllowedWhenConsumersArePerGroup : Bool
groupDependentAnalyticConstantsAreAllowedWhenConsumersArePerGroup = true

cutoffUniformityWithinFixedGroupMayStillBeRequired : Bool
cutoffUniformityWithinFixedGroupMayStillBeRequired = true

perGroupPaymentImpliesUniformAcrossGroupsPayment : Bool
perGroupPaymentImpliesUniformAcrossGroupsPayment = false

uniformAcrossGroupsPaymentIsStrictlyStrongerShape : Bool
uniformAcrossGroupsPaymentIsStrictlyStrongerShape = true

round449QuantifierFirewallLevel : ProofLevel
round449QuantifierFirewallLevel = machineChecked

round449ClayEndpointScopeAuditLevel : ProofLevel
round449ClayEndpointScopeAuditLevel = machineChecked
