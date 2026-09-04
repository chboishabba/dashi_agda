module DASHI.Analysis.NonArchimedeanMonsterCorrespondencePromotionKernelExact where

------------------------------------------------------------------------
-- SAME-OBJECT PROMOTION KERNEL FOR THE NON-ARCHIMEDEAN / MONSTER LANE
--
-- This mirrors DASHI's established Monster same-object discipline: matching
-- dimensions or characters are not enough.  A representation correspondence
-- requires a two-sided carrier rechart and equivariance for the relevant actor.
--
-- The source x3 permutation itself is not eligible to be the central Monster
-- 3B actor because their orders differ.  A future correspondence must therefore
-- target a multiplicity-space / normalizer actor or another explicitly named
-- restricted action.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Analysis.NonArchimedeanMonster3BActionSeparationExact as Separation


data MonsterActorRole : Set where
  central3BActor : MonsterActorRole
  multiplicitySpaceActor : MonsterActorRole
  normalizerActor : MonsterActorRole
  restrictedSubgroupActor : MonsterActorRole

actorRoleStatus : MonsterActorRole → Bool
actorRoleStatus central3BActor = false
actorRoleStatus multiplicitySpaceActor = true
actorRoleStatus normalizerActor = true
actorRoleStatus restrictedSubgroupActor = true

central3BActorRejectedForSourceTimesThree :
  actorRoleStatus central3BActor ≡ false
central3BActorRejectedForSourceTimesThree = refl

record EquivariantSameObject : Set₁ where
  field
    SourceState : Set
    MonsterState : Set
    SourceActor : Set
    MonsterActor : Set

    actorMap : SourceActor → MonsterActor
    sourceAct : SourceActor → SourceState → SourceState
    monsterAct : MonsterActor → MonsterState → MonsterState

    toMonster : SourceState → MonsterState
    fromMonster : MonsterState → SourceState

    fromAfterTo :
      (state : SourceState) → fromMonster (toMonster state) ≡ state
    toAfterFrom :
      (state : MonsterState) → toMonster (fromMonster state) ≡ state

    intertwines :
      (actor : SourceActor) →
      (state : SourceState) →
      toMonster (sourceAct actor state)
      ≡ monsterAct (actorMap actor) (toMonster state)

open EquivariantSameObject public

record CharacterObserverWeld
    (E : EquivariantSameObject) : Set₁ where
  field
    SourceClass : Set
    MonsterClass : Set
    TraceValue : Set

    classMap : SourceClass → MonsterClass
    sourceTrace : SourceClass → TraceValue
    monsterTrace : MonsterClass → TraceValue

    tracesAgree :
      (class : SourceClass) →
      sourceTrace class ≡ monsterTrace (classMap class)

open CharacterObserverWeld public

record RepresentationCorrespondenceReceipt : Set₁ where
  field
    actorRole : MonsterActorRole
    actorRoleAdmissible : actorRoleStatus actorRole ≡ true
    sameObject : EquivariantSameObject
    characterWeld : CharacterObserverWeld sameObject

open RepresentationCorrespondenceReceipt public

------------------------------------------------------------------------
-- BIDI promotion ladder.
------------------------------------------------------------------------

data PromotionCoordinate : Set where
  cardinalityCoordinate : PromotionCoordinate
  multiplicityFibreCoordinate : PromotionCoordinate
  actorRoleCoordinate : PromotionCoordinate
  carrierRechartCoordinate : PromotionCoordinate
  actionEquivarianceCoordinate : PromotionCoordinate
  classCharacterCoordinate : PromotionCoordinate
  representationReceiptCoordinate : PromotionCoordinate

representationPromotionCutset : List PromotionCoordinate
representationPromotionCutset =
  cardinalityCoordinate ∷
  multiplicityFibreCoordinate ∷
  actorRoleCoordinate ∷
  carrierRechartCoordinate ∷
  actionEquivarianceCoordinate ∷
  classCharacterCoordinate ∷
  representationReceiptCoordinate ∷
  []

record PromotionKernelBoundary : Set where
  constructor promotion-kernel-boundary
  field
    cardinalityCanSkipActionEquivariance : Bool
    characterEqualityCanSkipCarrierRechart : Bool
    matchingTraceCanPromoteSameRepresentation : Bool
    sourceTimesThreeCanUseCentral3BActor : Bool
    normalizerOrMultiplicityActorRemainsCandidate : Bool
    sameObjectNeedsTwoSidedRechartAndIntertwiner : Bool

canonicalPromotionKernelBoundary : PromotionKernelBoundary
canonicalPromotionKernelBoundary =
  promotion-kernel-boundary
    false false false false true true
