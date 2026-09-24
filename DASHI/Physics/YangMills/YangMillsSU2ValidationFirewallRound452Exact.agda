{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSU2ValidationFirewallRound452Exact where

------------------------------------------------------------------------
-- ROUND452 / SU(2) VALIDATION IS NOT A GENERIC COMPACT-SIMPLE PREMISE
--
-- A concrete SU(2) calculation can instantiate and validate a generic theorem.
-- It does not, by itself, prove or become a premise of
--
--   forall compact-simple G, Claim G.
--
-- This module keeps those two proof shapes separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

open import DASHI.Physics.YangMills.CompactLieProofLevel

GenericCompactSimplePayment :
  (Group : Set) → (Claim : Group → Set) → Set₁
GenericCompactSimplePayment Group Claim =
  ∀ group → Claim group

PointValidation :
  (Group : Set) → Group → (Claim : Group → Set) → Set
PointValidation Group selected Claim =
  Claim selected

genericPaymentInstantiatesAt :
  ∀ {Group : Set} {Claim : Group → Set} →
  GenericCompactSimplePayment Group Claim →
  ∀ selected →
  PointValidation Group selected Claim
genericPaymentInstantiatesAt generic selected =
  generic selected

record ExplicitValidationAt
    (Group : Set)
    (selected : Group)
    (Claim : Group → Set) : Set₁ where
  field
    validation : PointValidation Group selected Claim

open ExplicitValidationAt public

su2ExplicitValidationRequiredForGenericCompactSimpleConstruction : Bool
su2ExplicitValidationRequiredForGenericCompactSimpleConstruction = false

su2ValidationMayInstantiateGenericConstruction : Bool
su2ValidationMayInstantiateGenericConstruction = true

singleGroupValidationImpliesGenericCompactSimplePayment : Bool
singleGroupValidationImpliesGenericCompactSimplePayment = false

genericCompactSimplePaymentMayBeValidatedAtSU2 : Bool
genericCompactSimplePaymentMayBeValidatedAtSU2 = true

round452ValidationPremiseFirewallLevel : ProofLevel
round452ValidationPremiseFirewallLevel = machineChecked
