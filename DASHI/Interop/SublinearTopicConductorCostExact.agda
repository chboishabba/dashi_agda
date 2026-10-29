{-# OPTIONS --safe #-}
module DASHI.Interop.SublinearTopicConductorCostExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using (_≢_)

import DASHI.Interop.SLRWorldResearchIterationBudgetExact as Budget

------------------------------------------------------------------------
-- SUBLINEAR TOPIC CONDUCTOR CONTROL LAW
--
-- Runtime owner:
--   chboishabba/ITIR-suite
--   itir-mcp/src/itir_mcp/fleet_round_runner.py
--
-- Agda is the golden control-law owner.  The runtime cost receipt records:
--
-- C(T_k,W) =
--   alpha(T_k) * (UnblockedGoals / TotalGoals)
--              * min(W_cap, dim(SubEigens), W)
--   - TokenCost(W)
--
-- This module formalises the discrete worker-width law and authority
-- firewalls.  It does not claim floating-point parity for runtime alpha or
-- token-cost arithmetic.
------------------------------------------------------------------------

minNat : Nat → Nat → Nat
minNat zero _ = zero
minNat _ zero = zero
minNat (suc left) (suc right) = suc (minNat left right)

data TopicShape : Set where
  frontierBlocked : Nat → TopicShape
  sequential : TopicShape
  parallelBySubEigen : Nat → TopicShape

workerWidth : Nat → TopicShape → Nat
workerWidth cap (frontierBlocked blockers) = minNat cap blockers
workerWidth zero sequential = zero
workerWidth (suc cap) sequential = suc zero
workerWidth cap (parallelBySubEigen dimension) = minNat cap dimension

record DynamicConductorBoundary : Set where
  constructor dynamic-conductor-boundary
  field
    costFormulaReference : String
    workerCapacityIsBudgetNotModeSelector : Bool
    frontierBlockedWidthUsesBlockerCount : Bool
    sequentialWidthIsOneWhenCapacityPositive : Bool
    parallelWidthUsesSubEigenDimension : Bool
    lowerAlphaSubtopicsRemainPreserved : Bool
    lowerAlphaSubtopicsBecomeSequencedInternalPackets : Bool
    rolledPacketsRemainEligibleForCrossPollination : Bool
    alphaCreatesTruth : Bool
    alphaCreatesProofAuthority : Bool
    workerAllocationCreatesSemanticAuthority : Bool
    parallelDispatchRequiresNoTypedMeet : Bool
    candidateOnly : Bool

open DynamicConductorBoundary public

canonicalDynamicConductorBoundary : DynamicConductorBoundary
canonicalDynamicConductorBoundary =
  dynamic-conductor-boundary
    "C(T_k,W)=alpha(T_k)*(UnblockedGoals/TotalGoals)*min(W_cap,dim(SubEigens),W)-TokenCost(W)"
    true true true true
    true true true
    false false false
    true true

frontierBlockedWidthLaw :
  (cap blockers : Nat) →
  workerWidth cap (frontierBlocked blockers) ≡ minNat cap blockers
frontierBlockedWidthLaw cap blockers = refl

sequentialWidthLaw :
  (cap : Nat) →
  workerWidth (suc cap) sequential ≡ suc zero
sequentialWidthLaw cap = refl

parallelSubEigenWidthLaw :
  (cap dimension : Nat) →
  workerWidth cap (parallelBySubEigen dimension) ≡ minNat cap dimension
parallelSubEigenWidthLaw cap dimension = refl

fourBlockersWithTwentyWorkersUsesFour :
  workerWidth 20 (frontierBlocked 4) ≡ 4
fourBlockersWithTwentyWorkersUsesFour = refl

sequentialWithTwentyWorkersUsesOne :
  workerWidth 20 sequential ≡ 1
sequentialWithTwentyWorkersUsesOne = refl

fiveSubEigensWithTwentyWorkersUsesFive :
  workerWidth 20 (parallelBySubEigen 5) ≡ 5
fiveSubEigensWithTwentyWorkersUsesFive = refl

capacityDoesNotSelectMode :
  workerCapacityIsBudgetNotModeSelector canonicalDynamicConductorBoundary ≡ true
capacityDoesNotSelectMode = refl

lowerAlphaWorkIsPreserved :
  lowerAlphaSubtopicsRemainPreserved canonicalDynamicConductorBoundary ≡ true
lowerAlphaWorkIsPreserved = refl

lowerAlphaWorkIsSequencedInternally :
  lowerAlphaSubtopicsBecomeSequencedInternalPackets canonicalDynamicConductorBoundary ≡ true
lowerAlphaWorkIsSequencedInternally = refl

alphaDoesNotCreateTruth :
  alphaCreatesTruth canonicalDynamicConductorBoundary ≡ false
alphaDoesNotCreateTruth = refl

alphaDoesNotCreateProofAuthority :
  alphaCreatesProofAuthority canonicalDynamicConductorBoundary ≡ false
alphaDoesNotCreateProofAuthority = refl

allocationDoesNotCreateSemanticAuthority :
  workerAllocationCreatesSemanticAuthority canonicalDynamicConductorBoundary ≡ false
allocationDoesNotCreateSemanticAuthority = refl

parallelStillRequiresNoTypedMeet :
  parallelDispatchRequiresNoTypedMeet canonicalDynamicConductorBoundary ≡ true
parallelStillRequiresNoTypedMeet = refl


------------------------------------------------------------------------
-- FULL TWENTY-WORKER CONCURRENT SCHEDULE
--
-- A total function from Fin 20 occupies every slot.
-- Pairwise independence is supplied as typed noTypedMeet evidence.
------------------------------------------------------------------------

twentyWorkerCapacity : Nat
twentyWorkerCapacity = 20

twentyWorkerCapacityIsTwenty :
  twentyWorkerCapacity ≡ 20
twentyWorkerCapacityIsTwenty = refl

record FullTwentyWorkerSchedule
    (Goal : Set)
    (NoTypedMeet : Goal → Goal → Set) : Set₁ where
  constructor full-twenty-worker-schedule
  field
    assignment : Fin 20 → Goal
    GoalUnblocked : Goal → Set
    scheduledGoalUnblocked :
      (slot : Fin 20) →
      GoalUnblocked (assignment slot)
    GoalParetoEligible : Goal → Set
    scheduledGoalParetoEligible :
      (slot : Fin 20) →
      GoalParetoEligible (assignment slot)
    TopParetoRanked : Goal → Set
    scheduledGoalTopParetoRanked :
      (slot : Fin 20) →
      TopParetoRanked (assignment slot)
    distinctSlotsHaveDistinctGoals :
      (left right : Fin 20) →
      left ≢ right →
      assignment left ≢ assignment right
    pairwiseNoTypedMeet :
      (left right : Fin 20) →
      left ≢ right →
      NoTypedMeet (assignment left) (assignment right)

open FullTwentyWorkerSchedule public

record TwentyWorkerConcurrencyBoundary : Set where
  constructor twenty-worker-concurrency-boundary
  field
    capacity : Nat
    capacityIsTwenty : capacity ≡ 20
    allSlotsMustBeOccupied : Bool
    allSlotsMustBeOccupiedIsTrue :
      allSlotsMustBeOccupied ≡ true
    allGoalsMustBeUnblocked : Bool
    allGoalsMustBeUnblockedIsTrue :
      allGoalsMustBeUnblocked ≡ true
    allGoalsMustBeParetoEligible : Bool
    allGoalsMustBeParetoEligibleIsTrue :
      allGoalsMustBeParetoEligible ≡ true
    allGoalsMustBeTopParetoRanked : Bool
    allGoalsMustBeTopParetoRankedIsTrue :
      allGoalsMustBeTopParetoRanked ≡ true
    distinctSlotsRequireNoTypedMeet : Bool
    distinctSlotsRequireNoTypedMeetIsTrue :
      distinctSlotsRequireNoTypedMeet ≡ true
    serialModuloEightIsAcceptedAsTwentyWorkerSchedule : Bool
    serialModuloEightIsAcceptedAsTwentyWorkerScheduleIsFalse :
      serialModuloEightIsAcceptedAsTwentyWorkerSchedule ≡ false

open TwentyWorkerConcurrencyBoundary public

canonicalTwentyWorkerConcurrencyBoundary :
  TwentyWorkerConcurrencyBoundary
canonicalTwentyWorkerConcurrencyBoundary =
  twenty-worker-concurrency-boundary
    20 refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl

serialModuloEightIsNotFullTwentyWorkerConcurrency :
  serialModuloEightIsAcceptedAsTwentyWorkerSchedule
    canonicalTwentyWorkerConcurrencyBoundary
  ≡ false
serialModuloEightIsNotFullTwentyWorkerConcurrency = refl

budgetAnchor : Budget.WorldResearchIterationBudget
budgetAnchor = Budget.canonicalWorldResearchIterationBudget
