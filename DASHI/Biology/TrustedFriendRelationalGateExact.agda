module DASHI.Biology.TrustedFriendRelationalGateExact where

open import DASHI.Core.Prelude

import DASHI.Biology.SocialEcologicalAffordanceConeExact as Ecology
import DASHI.Biology.TrustedFriendRelationalScaffoldingExact as Friend

------------------------------------------------------------------------
-- TRUSTED FRIEND AS A RELATION-ONLY GATE COORDINATE
--
-- This bridge strengthens the existing safe-person/friendship work by holding
-- person, built environment, social norms and institution fixed while changing
-- only the relation coordinate.
--
-- It therefore isolates the exact theorem shape discussed in the current
-- neurodivergent social-ecology thread:
--
--   same person + same place + same norms + same institution
--   + different trusted relation
--   -> different realised option cone.
--
-- The trusted friend remains contextual / regulatory scaffolding, not decision
-- authority.  The richer #606 relational-coregulation and reachable-subfabric
-- owners remain the eventual generic dynamic owner after ancestry convergence.
------------------------------------------------------------------------

alonePartialEcology : Ecology.Ecology
alonePartialEcology =
  Ecology.ecology
    Ecology.denseUncontrolledSpace
    Ecology.conformityDemandNorms
    Ecology.partialPermissionRegime
    Ecology.aloneRelation

trustedFriendPartialEcology : Ecology.Ecology
trustedFriendPartialEcology =
  Ecology.ecology
    Ecology.denseUncontrolledSpace
    Ecology.conformityDemandNorms
    Ecology.partialPermissionRegime
    Ecology.trustedFriendRelation

sameBuiltEnvironment :
  Ecology.built alonePartialEcology
  ≡ Ecology.built trustedFriendPartialEcology
sameBuiltEnvironment = refl

sameSocialNorms :
  Ecology.norms alonePartialEcology
  ≡ Ecology.norms trustedFriendPartialEcology
sameSocialNorms = refl

sameInstitution :
  Ecology.institution alonePartialEcology
  ≡ Ecology.institution trustedFriendPartialEcology
sameInstitution = refl

relationCoordinateDiffers :
  Ecology.relation alonePartialEcology
  ≡ Ecology.relation trustedFriendPartialEcology → ⊥
relationCoordinateDiffers ()

aloneRemainClosed :
  Ecology.available
    Ecology.canonicalAutisticPerson
    alonePartialEcology
    Ecology.remainAction
  ≡ false
aloneRemainClosed = refl

friendRemainOpen :
  Ecology.available
    Ecology.canonicalAutisticPerson
    trustedFriendPartialEcology
    Ecology.remainAction
  ≡ true
friendRemainOpen = refl

aloneRecoveryClosed :
  Ecology.available
    Ecology.canonicalAutisticPerson
    alonePartialEcology
    Ecology.recoverAction
  ≡ false
aloneRecoveryClosed = refl

friendRecoveryOpen :
  Ecology.available
    Ecology.canonicalAutisticPerson
    trustedFriendPartialEcology
    Ecology.recoverAction
  ≡ true
friendRecoveryOpen = refl

relationOnlyChangeCanOpenRemain :
  Ecology.available
    Ecology.canonicalAutisticPerson
    alonePartialEcology
    Ecology.remainAction
  ≡ Ecology.available
      Ecology.canonicalAutisticPerson
      trustedFriendPartialEcology
      Ecology.remainAction
  → ⊥
relationOnlyChangeCanOpenRemain ()

relationOnlyChangeCanOpenRecovery :
  Ecology.available
    Ecology.canonicalAutisticPerson
    alonePartialEcology
    Ecology.recoverAction
  ≡ Ecology.available
      Ecology.canonicalAutisticPerson
      trustedFriendPartialEcology
      Ecology.recoverAction
  → ⊥
relationOnlyChangeCanOpenRecovery ()

------------------------------------------------------------------------
-- Epistemic support and affordance support remain separate proof surfaces.
------------------------------------------------------------------------

friendAddsContextualObservation :
  Friend.selfObserver Friend.benignAmbiguity
  ≡ Friend.selfObserver Friend.hostileAmbiguity
friendAddsContextualObservation =
  Friend.sameSelfObservationAcrossDifferentSituations

friendJointObservationSeparates :
  Friend.jointObserver Friend.benignAmbiguity
  ≡ Friend.jointObserver Friend.hostileAmbiguity → ⊥
friendJointObservationSeparates =
  Friend.jointObservationDistinguishesThoseSituations

record TrustedFriendRelationalGateBoundary : Set where
  constructor trusted-friend-relational-gate-boundary
  field
    friendEffectRequiresChangingPerson : Bool
    friendEffectRequiresChangingPersonIsFalse :
      friendEffectRequiresChangingPerson ≡ false
    friendEffectRequiresChangingBuiltEnvironment : Bool
    friendEffectRequiresChangingBuiltEnvironmentIsFalse :
      friendEffectRequiresChangingBuiltEnvironment ≡ false
    relationCoordinateCanChangeRealizedOptionCone : Bool
    relationCoordinateCanChangeRealizedOptionConeIsTrue :
      relationCoordinateCanChangeRealizedOptionCone ≡ true
    contextualObservationEqualsDecisionAuthority : Bool
    contextualObservationEqualsDecisionAuthorityIsFalse :
      contextualObservationEqualsDecisionAuthority ≡ false
    everyTrustedFriendAlwaysOpensEveryAction : Bool
    everyTrustedFriendAlwaysOpensEveryActionIsFalse :
      everyTrustedFriendAlwaysOpensEveryAction ≡ false

canonicalTrustedFriendRelationalGateBoundary :
  TrustedFriendRelationalGateBoundary
canonicalTrustedFriendRelationalGateBoundary =
  trusted-friend-relational-gate-boundary
    false refl
    false refl
    true refl
    false refl
    false refl
