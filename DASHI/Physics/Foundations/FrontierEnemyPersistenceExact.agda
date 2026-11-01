module DASHI.Physics.Foundations.FrontierEnemyPersistenceExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Generic political-order carrier.  Concrete historical instantiations must
-- still provide evidence; this record does not manufacture them.

record PoliticalOrder
  (Homeland Enemy Frontier Frame : Set) : Set where
  constructor politicalOrder
  field
    homeland : Homeland
    enemy : Enemy
    frontier : Frontier
    frame : Frame

open PoliticalOrder public

------------------------------------------------------------------------
-- Frontier paradox: a zone may be represented as outside full inclusion while
-- simultaneously being treated as necessary to the core's security.

record FrontierPosition : Set where
  constructor frontierPosition
  field
    includedInProtectedCore : Bool
    requiredForCoreSecurity : Bool

open FrontierPosition public

canonicalFrontierParadox : FrontierPosition
canonicalFrontierParadox = frontierPosition false true

frontierExcludedFromCore :
  includedInProtectedCore canonicalFrontierParadox ≡ false
frontierExcludedFromCore = refl

frontierRequiredForSecurity :
  requiredForCoreSecurity canonicalFrontierParadox ≡ true
frontierRequiredForSecurity = refl

------------------------------------------------------------------------
-- Permanent-enemy effect.  Removing one concrete actor does not definitionally
-- remove an abstract enemy category into which later actors can be inserted.

data ConcreteEnemyEpoch : Set where
  firstConcreteEnemy : ConcreteEnemyEpoch
  laterConcreteEnemy : ConcreteEnemyEpoch

data AbstractEnemyType : Set where
  recurringAbsoluteEnemy : AbstractEnemyType

data Presence : Set where
  present : Presence
  absent : Presence

abstractEnemyOf : ConcreteEnemyEpoch → AbstractEnemyType
abstractEnemyOf firstConcreteEnemy = recurringAbsoluteEnemy
abstractEnemyOf laterConcreteEnemy = recurringAbsoluteEnemy

defeat : ConcreteEnemyEpoch → Presence
defeat firstConcreteEnemy = absent
defeat laterConcreteEnemy = absent

firstEnemyDefeated : defeat firstConcreteEnemy ≡ absent
firstEnemyDefeated = refl

categoryPersistsAfterFirstDefeat :
  abstractEnemyOf firstConcreteEnemy
  ≡
  abstractEnemyOf laterConcreteEnemy
categoryPersistsAfterFirstDefeat = refl

firstAndLaterEnemiesAreDistinct :
  firstConcreteEnemy ≡ laterConcreteEnemy → ⊥
firstAndLaterEnemiesAreDistinct ()

------------------------------------------------------------------------
-- A security apparatus can therefore persist by classifying a later actor in
-- the same abstract type.  The theorem records the finite mechanism only.

data SecurityStage : Set where
  abstractEnemyStage : SecurityStage
  permanentFrontierStage : SecurityStage
  permanentSurveillanceStage : SecurityStage
  permanentMobilisationStage : SecurityStage

nextSecurityStage : SecurityStage → SecurityStage
nextSecurityStage abstractEnemyStage = permanentFrontierStage
nextSecurityStage permanentFrontierStage = permanentSurveillanceStage
nextSecurityStage permanentSurveillanceStage = permanentMobilisationStage
nextSecurityStage permanentMobilisationStage = permanentMobilisationStage

abstractEnemyToMobilisation :
  nextSecurityStage
    (nextSecurityStage
      (nextSecurityStage abstractEnemyStage))
  ≡ permanentMobilisationStage
abstractEnemyToMobilisation = refl

record FrontierEnemyPersistenceBoundary : Set where
  constructor frontierEnemyPersistenceBoundary
  field
    genericCarrierProvesConcreteHistoricalInstance : Bool
    genericCarrierProvesConcreteHistoricalInstanceIsFalse :
      genericCarrierProvesConcreteHistoricalInstance ≡ false

    defeatingActorDissolvesEnemyCategoryAutomatically : Bool
    defeatingActorDissolvesEnemyCategoryAutomaticallyIsFalse :
      defeatingActorDissolvesEnemyCategoryAutomatically ≡ false

    securityDependenceProvesJustTerritorialControl : Bool
    securityDependenceProvesJustTerritorialControlIsFalse :
      securityDependenceProvesJustTerritorialControl ≡ false

open FrontierEnemyPersistenceBoundary public

canonicalFrontierEnemyPersistenceBoundary :
  FrontierEnemyPersistenceBoundary
canonicalFrontierEnemyPersistenceBoundary =
  frontierEnemyPersistenceBoundary
    false refl
    false refl
    false refl
