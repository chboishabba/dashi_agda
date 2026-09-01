module DASHI.Computation.PathfindingTemporalFibreFamilyExact where

-- Cross-algorithm temporal fibre taxonomy.
-- Algorithms differ not only in their residual carrier at one instant, but in
-- the lawful evolution of that carrier over search time.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Computation.PathfindingTemporalFibreEvolutionExact as Temporal
import DASHI.Computation.BMSSPTemporalStableFrontierFibreExact as BMSSP

------------------------------------------------------------------------
-- 1. Named temporal evolution roles.
------------------------------------------------------------------------

data PathfindingEvolutionRole : Set where
  bfsAdvanceLayer : PathfindingEvolutionRole
  dijkstraSettleMinimum : PathfindingEvolutionRole
  bellmanFordRefineRound : PathfindingEvolutionRole
  aStarRefinePlateau : PathfindingEvolutionRole
  bidirectionalAdvanceMeetingCut : PathfindingEvolutionRole
  bmsspExposeCompressRecurse : PathfindingEvolutionRole
  incrementalReopenRepair : PathfindingEvolutionRole

record TemporalAlgorithmIdentity : Set where
  constructor temporalAlgorithmIdentity
  field
    role : PathfindingEvolutionRole
    residualCanChange : Bool
    residualCanReopen : Bool
    observationAtOneTimeDeterminesWholeFuture : Bool
    observationAtOneTimeDeterminesWholeFutureIsFalse :
      observationAtOneTimeDeterminesWholeFuture ≡ false

open TemporalAlgorithmIdentity public

bfsTemporalIdentity : TemporalAlgorithmIdentity
bfsTemporalIdentity = temporalAlgorithmIdentity bfsAdvanceLayer true false false refl

dijkstraTemporalIdentity : TemporalAlgorithmIdentity
dijkstraTemporalIdentity = temporalAlgorithmIdentity dijkstraSettleMinimum true false false refl

bellmanFordTemporalIdentity : TemporalAlgorithmIdentity
bellmanFordTemporalIdentity = temporalAlgorithmIdentity bellmanFordRefineRound true false false refl

aStarTemporalIdentity : TemporalAlgorithmIdentity
aStarTemporalIdentity = temporalAlgorithmIdentity aStarRefinePlateau true true false refl

bidirectionalTemporalIdentity : TemporalAlgorithmIdentity
bidirectionalTemporalIdentity = temporalAlgorithmIdentity bidirectionalAdvanceMeetingCut true false false refl

bmsspTemporalIdentity : TemporalAlgorithmIdentity
bmsspTemporalIdentity = temporalAlgorithmIdentity bmsspExposeCompressRecurse true true false refl

incrementalTemporalIdentity : TemporalAlgorithmIdentity
incrementalTemporalIdentity = temporalAlgorithmIdentity incrementalReopenRepair true true false refl

------------------------------------------------------------------------
-- 2. Family firewall.
------------------------------------------------------------------------

record TemporalPathfindingFamilyBoundary : Set where
  constructor temporalPathfindingFamilyBoundary
  field
    allAlgorithmsHaveStaticResidualCarrier : Bool
    allAlgorithmsHaveStaticResidualCarrierIsFalse :
      allAlgorithmsHaveStaticResidualCarrier ≡ false

    sameVisibleObservationNowMeansSameFutureCone : Bool
    sameVisibleObservationNowMeansSameFutureConeIsFalse :
      sameVisibleObservationNowMeansSameFutureCone ≡ false

    dynamicRepairCanReopenOldResidual : Bool
    dynamicRepairCanReopenOldResidualIsTrue :
      dynamicRepairCanReopenOldResidual ≡ true

    bmsspTailMayChangeAcrossRecursiveStep : Bool
    bmsspTailMayChangeAcrossRecursiveStepIsTrue :
      bmsspTailMayChangeAcrossRecursiveStep ≡ true

canonicalTemporalPathfindingFamilyBoundary : TemporalPathfindingFamilyBoundary
canonicalTemporalPathfindingFamilyBoundary =
  temporalPathfindingFamilyBoundary false refl false refl true refl true refl
