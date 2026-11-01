{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClaySU2ValidationFirewallRound478Exact where

------------------------------------------------------------------------
-- GOAL-1 / ROUND478: VALIDATION IS NOT A GENERIC PREMISE
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)

open import DASHI.Physics.YangMills.CompactLieProofLevel

GenericPayment :
  (Group : Set) → (Claim : Group → Set) → Set₁
GenericPayment Group Claim =
  ∀ group → Claim group

ValidationAt :
  (Group : Set) → Group → (Claim : Group → Set) → Set
ValidationAt Group selected Claim =
  Claim selected

instantiateGeneric :
  ∀ {Group : Set} {Claim : Group → Set} →
  GenericPayment Group Claim →
  ∀ group →
  ValidationAt Group group Claim
instantiateGeneric generic group =
  generic group

su2ValidationRequiredForGenericConstruction : Bool
su2ValidationRequiredForGenericConstruction = false

genericConstructionMayBeValidatedAtSU2 : Bool
genericConstructionMayBeValidatedAtSU2 = true

singleGroupValidationPromotesToAllCompactSimpleGroups : Bool
singleGroupValidationPromotesToAllCompactSimpleGroups = false

round478ValidationFirewallCompilerLevel : ProofLevel
round478ValidationFirewallCompilerLevel = machineChecked
