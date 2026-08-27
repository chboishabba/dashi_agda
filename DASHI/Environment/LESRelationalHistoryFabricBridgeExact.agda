module DASHI.Environment.LESRelationalHistoryFabricBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Core.RelationalHistoryFabricExact as Fabric
import DASHI.Environment.LESResearchCrossPollinationRound7Exact as LES7
import DASHI.Environment.ThreeSistersLESRelationalComplementarityBridgeExact as ThreeSisters

------------------------------------------------------------------------
-- LES RELATIONAL-HISTORY FABRIC
--
-- This bridge composes, without identifying, two already-separate axes:
--
--   history axis:
--     LES Round 7 synthetic management history / continuation structure
--
--   relation axis:
--     Three Sisters component inventory versus relational arrangement
--
-- The four-state product below is DASHI synthetic mathematics.  It is not an
-- empirical transition table, does not estimate agricultural outcomes, and
-- contains no private legal, commercial, family, client, or case facts.
------------------------------------------------------------------------

data SituatedPlanningState : Set where
  shortIsolated shortRelated longIsolated longRelated : SituatedPlanningState

data CoarsePlanningObservation : Set where
  sameCurrentPlanningSummary : CoarsePlanningObservation

data GateCode : Set where
  rapidTransitionGate stagedTransitionGate : GateCode

data ReachableCode : Set where
  rapidIsolatedReachable rapidRelatedReachable
  stagedIsolatedReachable stagedRelatedReachable : ReachableCode

data AffordanceCode : Set where
  isolatedAffordance relatedAffordance : AffordanceCode

data JointFutureConeCode : Set where
  shortIsolatedCone shortRelatedCone longIsolatedCone longRelatedCone : JointFutureConeCode

historyCode : SituatedPlanningState → LES7.ManagementHistory
historyCode shortIsolated = LES7.shortHorizonConfiguration
historyCode shortRelated = LES7.shortHorizonConfiguration
historyCode longIsolated = LES7.longHorizonConfiguration
historyCode longRelated = LES7.longHorizonConfiguration

relationCode : SituatedPlanningState → ThreeSisters.CroppingRelation
relationCode shortIsolated = ThreeSisters.isolatedComponentStands
relationCode longIsolated = ThreeSisters.isolatedComponentStands
relationCode shortRelated = ThreeSisters.coCultivatedThreeSisters
relationCode longRelated = ThreeSisters.coCultivatedThreeSisters

gateCode : SituatedPlanningState → GateCode
gateCode shortIsolated = rapidTransitionGate
gateCode shortRelated = rapidTransitionGate
gateCode longIsolated = stagedTransitionGate
gateCode longRelated = stagedTransitionGate

reachableCode : SituatedPlanningState → ReachableCode
reachableCode shortIsolated = rapidIsolatedReachable
reachableCode shortRelated = rapidRelatedReachable
reachableCode longIsolated = stagedIsolatedReachable
reachableCode longRelated = stagedRelatedReachable

affordanceCode : SituatedPlanningState → AffordanceCode
affordanceCode shortIsolated = isolatedAffordance
affordanceCode longIsolated = isolatedAffordance
affordanceCode shortRelated = relatedAffordance
affordanceCode longRelated = relatedAffordance

jointFutureCone : SituatedPlanningState → JointFutureConeCode
jointFutureCone shortIsolated = shortIsolatedCone
jointFutureCone shortRelated = shortRelatedCone
jointFutureCone longIsolated = longIsolatedCone
jointFutureCone longRelated = longRelatedCone

observePlanning : SituatedPlanningState → CoarsePlanningObservation
observePlanning _ = sameCurrentPlanningSummary

lesRelationalHistoryFabric : Fabric.RelationalHistoryFabric
lesRelationalHistoryFabric =
  record
    { SituatedState = SituatedPlanningState
    ; Observation = CoarsePlanningObservation
    ; HistoryCode = LES7.ManagementHistory
    ; RelationCode = ThreeSisters.CroppingRelation
    ; GateCode = GateCode
    ; ReachableCode = ReachableCode
    ; AffordanceCode = AffordanceCode
    ; FutureConeCode = JointFutureConeCode
    ; observe = observePlanning
    ; historyOf = historyCode
    ; relationOf = relationCode
    ; gateOf = gateCode
    ; reachableOf = reachableCode
    ; affordanceOf = affordanceCode
    ; futureConeOf = jointFutureCone
    ; fabricReading =
        "A synthetic LES planning state carries history and relational organisation as independent coordinates; the same coarse present summary can hide different reachable and future-cone codes."
    }

------------------------------------------------------------------------
-- History essentiality at fixed relation.
------------------------------------------------------------------------

historyEssentialAtFixedIsolatedRelation :
  Fabric.HistoryEssentialForFuture lesRelationalHistoryFabric
historyEssentialAtFixedIsolatedRelation =
  record
    { historyLeft = shortIsolated
    ; historyRight = longIsolated
    ; historySameObservation = refl
    ; historyRelationHeldFixed = refl
    ; historyActuallyDiffers = λ ()
    ; historyFutureDiffers = λ ()
    }

historyAxisBlocksPresentOnlyFutureModel :
  NonFactor.FactorsThrough observePlanning jointFutureCone → ⊥
historyAxisBlocksPresentOnlyFutureModel =
  Fabric.historyEssentialBlocksPresentOnlyFutureModel
    historyEssentialAtFixedIsolatedRelation

------------------------------------------------------------------------
-- Relation essentiality at fixed history.
------------------------------------------------------------------------

relationEssentialAtFixedShortHistory :
  Fabric.RelationEssentialForFuture lesRelationalHistoryFabric
relationEssentialAtFixedShortHistory =
  record
    { relationLeft = shortIsolated
    ; relationRight = shortRelated
    ; relationSameObservation = refl
    ; relationHistoryHeldFixed = refl
    ; relationActuallyDiffers = λ ()
    ; relationFutureDiffers = λ ()
    }

relationAxisBlocksPresentOnlyFutureModel :
  NonFactor.FactorsThrough observePlanning jointFutureCone → ⊥
relationAxisBlocksPresentOnlyFutureModel =
  Fabric.relationEssentialBlocksPresentOnlyFutureModel
    relationEssentialAtFixedShortHistory

------------------------------------------------------------------------
-- Partial propagation is intentionally weaker than the generic full chain.
--
-- With relation held fixed, the synthetic LES history contrast changes gate,
-- reachable code and future cone.  It does NOT change the relation-derived
-- affordance code in this bridge.  This blocks accidental promotion of the
-- product witness into a causal claim that history changes Three Sisters
-- complementarity itself.
------------------------------------------------------------------------

historyChangesGateAtFixedRelatedRelation :
  gateCode shortRelated ≡ gateCode longRelated → ⊥
historyChangesGateAtFixedRelatedRelation ()

historyChangesReachableAtFixedRelatedRelation :
  reachableCode shortRelated ≡ reachableCode longRelated → ⊥
historyChangesReachableAtFixedRelatedRelation ()

historyPreservesRelationDerivedAffordance :
  affordanceCode shortRelated ≡ affordanceCode longRelated
historyPreservesRelationDerivedAffordance = refl

historyChangesFutureAtFixedRelatedRelation :
  jointFutureCone shortRelated ≡ jointFutureCone longRelated → ⊥
historyChangesFutureAtFixedRelatedRelation ()

relationChangesAffordanceAtFixedShortHistory :
  affordanceCode shortIsolated ≡ affordanceCode shortRelated → ⊥
relationChangesAffordanceAtFixedShortHistory ()

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record LESRelationalHistoryFabricBoundary : Set where
  constructor lesRelationalHistoryFabricBoundary
  field
    historyAndRelationAreSameAxis : Bool
    historyAndRelationAreSameAxisIsFalse :
      historyAndRelationAreSameAxis ≡ false

    threeSistersComplementarityProvesLESPathDependence : Bool
    threeSistersComplementarityProvesLESPathDependenceIsFalse :
      threeSistersComplementarityProvesLESPathDependence ≡ false

    historyAutomaticallyChangesRelationalAffordance : Bool
    historyAutomaticallyChangesRelationalAffordanceIsFalse :
      historyAutomaticallyChangesRelationalAffordance ≡ false

    syntheticProductIsEmpiricalAgriculturalModel : Bool
    syntheticProductIsEmpiricalAgriculturalModelIsFalse :
      syntheticProductIsEmpiricalAgriculturalModel ≡ false

    privateCaseFactsEncoded : Bool
    privateCaseFactsEncodedIsFalse :
      privateCaseFactsEncoded ≡ false

canonicalLESRelationalHistoryFabricBoundary :
  LESRelationalHistoryFabricBoundary
canonicalLESRelationalHistoryFabricBoundary =
  lesRelationalHistoryFabricBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
