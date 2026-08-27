module DASHI.Biology.TrustedFriendEcologyInteractionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

import DASHI.Biology.NeurodivergentSocialEcologySourceRegistryExact as Sources
import DASHI.Biology.SocialEcologicalAffordanceConeExact as Ecology
import DASHI.Biology.TrustedFriendRelationalGateExact as FriendGate

------------------------------------------------------------------------
-- TRUSTED-FRIEND x ECOLOGY INTERACTION
--
-- The previous relation-only bridge proved that changing only the relation
-- coordinate can open remain/recovery in one fixed ecology.  This module asks
-- the stronger question: is that relational effect itself context-free?
--
-- Answer in the finite specimen: no.
--
-- In a dense/conformity-demanding partially permissive ecology, a trusted
-- friend changes remain from closed to open.  In an adjustable/low-demand
-- partially permissive ecology, remain is already open when alone, so adding a
-- trusted friend does not add another unit of availability.
--
-- This is an interaction theorem, not an empirical effect-size model.  The
-- Nat codes below are finite structural codes only.  Once PR #620 ancestry is
-- available, this file should become a thin adapter to the generic binary
-- interaction/nonseparability owner there.
------------------------------------------------------------------------

data EcologyCondition : Set where
  highDemandCondition repairedCondition : EcologyCondition

data RelationCondition : Set where
  aloneCondition trustedFriendCondition : RelationCondition

ecologyFor : EcologyCondition → RelationCondition → Ecology.Ecology
ecologyFor highDemandCondition aloneCondition = FriendGate.alonePartialEcology
ecologyFor highDemandCondition trustedFriendCondition =
  FriendGate.trustedFriendPartialEcology
ecologyFor repairedCondition aloneCondition =
  Ecology.ecology
    Ecology.adjustableRetreatSpace
    Ecology.lowDemandNorms
    Ecology.partialPermissionRegime
    Ecology.aloneRelation
ecologyFor repairedCondition trustedFriendCondition =
  Ecology.ecology
    Ecology.adjustableRetreatSpace
    Ecology.lowDemandNorms
    Ecology.partialPermissionRegime
    Ecology.trustedFriendRelation

------------------------------------------------------------------------
-- Exact realized remain surface from the existing social-ecology owner.
------------------------------------------------------------------------

highDemandAloneRemainClosed :
  Ecology.available
    Ecology.canonicalAutisticPerson
    (ecologyFor highDemandCondition aloneCondition)
    Ecology.remainAction
  ≡ false
highDemandAloneRemainClosed = refl

highDemandFriendRemainOpen :
  Ecology.available
    Ecology.canonicalAutisticPerson
    (ecologyFor highDemandCondition trustedFriendCondition)
    Ecology.remainAction
  ≡ true
highDemandFriendRemainOpen = refl

repairedAloneRemainOpen :
  Ecology.available
    Ecology.canonicalAutisticPerson
    (ecologyFor repairedCondition aloneCondition)
    Ecology.remainAction
  ≡ true
repairedAloneRemainOpen = refl

repairedFriendRemainOpen :
  Ecology.available
    Ecology.canonicalAutisticPerson
    (ecologyFor repairedCondition trustedFriendCondition)
    Ecology.remainAction
  ≡ true
repairedFriendRemainOpen = refl

------------------------------------------------------------------------
-- Finite Nat coding of the exact Bool surface.
--
--     alone   friend
-- high   0       1
-- repair 1       1
--
-- The code is intentionally not a clinical/support score.  It exists only to
-- expose the algebraic interaction obstruction.
------------------------------------------------------------------------

remainCode : EcologyCondition → RelationCondition → Nat
remainCode highDemandCondition aloneCondition = 0
remainCode highDemandCondition trustedFriendCondition = 1
remainCode repairedCondition aloneCondition = 1
remainCode repairedCondition trustedFriendCondition = 1

highDemandFriendGain :
  remainCode highDemandCondition trustedFriendCondition
  ≡ remainCode highDemandCondition aloneCondition + 1
highDemandFriendGain = refl

repairedFriendAddsNoAvailabilityUnit :
  remainCode repairedCondition trustedFriendCondition
  ≡ remainCode repairedCondition aloneCondition + 0
repairedFriendAddsNoAvailabilityUnit = refl

highDemandFriendChangesRemain :
  remainCode highDemandCondition trustedFriendCondition
  ≡ remainCode highDemandCondition aloneCondition → ⊥
highDemandFriendChangesRemain ()

repairedFriendLeavesRemainCodeUnchanged :
  remainCode repairedCondition trustedFriendCondition
  ≡ remainCode repairedCondition aloneCondition
repairedFriendLeavesRemainCodeUnchanged = refl

------------------------------------------------------------------------
-- No context-free additive "friend bonus" fits both environments.
--
-- Such a model would require one Nat bonus b satisfying
--
--   high-demand: 1 = 0 + b
--   repaired:    1 = 1 + b.
--
-- b = 0 fails the first equation; every successor b fails the second.
------------------------------------------------------------------------

record ContextFreeFriendBonus : Set where
  constructor context-free-friend-bonus
  field
    bonus : Nat
    highDemandFit :
      remainCode highDemandCondition trustedFriendCondition
      ≡ remainCode highDemandCondition aloneCondition + bonus
    repairedFit :
      remainCode repairedCondition trustedFriendCondition
      ≡ remainCode repairedCondition aloneCondition + bonus

open ContextFreeFriendBonus public

noContextFreeFriendBonus : ContextFreeFriendBonus → ⊥
noContextFreeFriendBonus model with bonus model
... | zero with highDemandFit model
...   | ()
... | suc n with repairedFit model
...   | ()

------------------------------------------------------------------------
-- Scope / source boundary.
------------------------------------------------------------------------

friendshipSource : Sources.SourceReference
friendshipSource = Sources.friendshipTrust2025

supportContextSource : Sources.SourceReference
supportContextSource = Sources.supportTranslation2024

builtEnvironmentSource : Sources.SourceReference
builtEnvironmentSource = Sources.builtEnvironment2026

record TrustedFriendEcologyInteractionBoundary : Set where
  constructor trusted-friend-ecology-interaction-boundary
  field
    friendEffectIsContextFreeAdditiveBonus : Bool
    friendEffectIsContextFreeAdditiveBonusIsFalse :
      friendEffectIsContextFreeAdditiveBonus ≡ false
    sameTrustedRelationHasSameEffectInEveryEcology : Bool
    sameTrustedRelationHasSameEffectInEveryEcologyIsFalse :
      sameTrustedRelationHasSameEffectInEveryEcology ≡ false
    relationAndEcologyCanInteractInRealizedAffordance : Bool
    relationAndEcologyCanInteractInRealizedAffordanceIsTrue :
      relationAndEcologyCanInteractInRealizedAffordance ≡ true
    finiteCodeIsEmpiricalFriendshipEffectSize : Bool
    finiteCodeIsEmpiricalFriendshipEffectSizeIsFalse :
      finiteCodeIsEmpiricalFriendshipEffectSize ≡ false
    trustedFriendBecomesDecisionAuthority : Bool
    trustedFriendBecomesDecisionAuthorityIsFalse :
      trustedFriendBecomesDecisionAuthority ≡ false

canonicalTrustedFriendEcologyInteractionBoundary :
  TrustedFriendEcologyInteractionBoundary
canonicalTrustedFriendEcologyInteractionBoundary =
  trusted-friend-ecology-interaction-boundary
    false refl
    false refl
    true refl
    false refl
    false refl
