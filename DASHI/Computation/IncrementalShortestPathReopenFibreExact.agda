module DASHI.Computation.IncrementalShortestPathReopenFibreExact where

-- Generic D*/LPA*-style temporal repair fibre.
-- A graph-cost update does not force total recomputation: it invalidates a
-- typed subset of previously settled information and reopens only the affected
-- residual fibre.  This owner captures the representation law, not a complete
-- implementation of either named algorithm.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; suc)

------------------------------------------------------------------------
-- 1. Stable temporal repair state.
------------------------------------------------------------------------

data RepairStatus : Set where
  consistent inconsistent reopened : RepairStatus

record IncrementalSearchState : Set where
  constructor incrementalSearchState
  field
    visibleShortestPathCode : Nat
    retainedSearchCode : Nat
    changedEdgeCode : Nat
    repairStatus : RepairStatus

open IncrementalSearchState public

record RepairObservation : Set where
  constructor repairObservation
  field
    visiblePathCode : Nat
    status : RepairStatus

open RepairObservation public

observeRepair : IncrementalSearchState → RepairObservation
observeRepair s = repairObservation (visibleShortestPathCode s) (repairStatus s)

------------------------------------------------------------------------
-- 2. Update/repair transition.
------------------------------------------------------------------------

record IncrementalRepairStep : Set₁ where
  constructor incrementalRepairStep
  field
    applyCostChange : IncrementalSearchState → IncrementalSearchState
    repair : IncrementalSearchState → IncrementalSearchState

    unaffectedVisiblePathMayPersist :
      (s : IncrementalSearchState) → Set

    changedInformationMayReopenResidual :
      (s : IncrementalSearchState) → Set

open IncrementalRepairStep public

------------------------------------------------------------------------
-- 3. Reopening is a temporal fibre operation, not a fresh-state identity.
------------------------------------------------------------------------

record ReopenReceipt
  (R : IncrementalRepairStep)
  (s : IncrementalSearchState) : Set where
  constructor reopenReceipt
  field
    before : IncrementalSearchState
    afterChange : IncrementalSearchState
    afterRepair : IncrementalSearchState

    beforeExact : before ≡ s
    afterChangeExact : afterChange ≡ applyCostChange R s
    afterRepairExact : afterRepair ≡ repair R (applyCostChange R s)

open ReopenReceipt public

record IncrementalReopenBoundary : Set where
  constructor incrementalReopenBoundary
  field
    costChangeRequiresDiscardingAllRetainedSearchState : Bool
    costChangeRequiresDiscardingAllRetainedSearchStateIsFalse :
      costChangeRequiresDiscardingAllRetainedSearchState ≡ false

    affectedResidualMayBeReopened : Bool
    affectedResidualMayBeReopenedIsTrue :
      affectedResidualMayBeReopened ≡ true

    visiblePathAloneDeterminesRepairWork : Bool
    visiblePathAloneDeterminesRepairWorkIsFalse :
      visiblePathAloneDeterminesRepairWork ≡ false

    sameVisiblePathBeforeUpdateMeansSameFutureRepairCone : Bool
    sameVisiblePathBeforeUpdateMeansSameFutureRepairConeIsFalse :
      sameVisiblePathBeforeUpdateMeansSameFutureRepairCone ≡ false

canonicalIncrementalReopenBoundary : IncrementalReopenBoundary
canonicalIncrementalReopenBoundary =
  incrementalReopenBoundary false refl true refl false refl false refl
