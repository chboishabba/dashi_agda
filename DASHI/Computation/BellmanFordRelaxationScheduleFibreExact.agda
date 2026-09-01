module DASHI.Computation.BellmanFordRelaxationScheduleFibreExact where

-- Bellman--Ford fibre: edge-relaxation schedule is residual only under an
-- explicit confluence/commutation witness for the observation being consumed.
-- This owner intentionally does not assert that arbitrary in-place schedules
-- are interchangeable without such a witness.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)

record RelaxationRoundState : Set where
  constructor relaxationRoundState
  field
    completedRounds : Nat
    distanceSummary : Nat
    scheduleCode : Bool

open RelaxationRoundState public

record RelaxationObservation : Set where
  constructor relaxationObservation
  field observedRounds observedDistanceSummary : Nat

observeRelaxation : RelaxationRoundState → RelaxationObservation
observeRelaxation s =
  relaxationObservation (completedRounds s) (distanceSummary s)

data ScheduleSwap : Set where identitySchedule swapSchedule : ScheduleSwap

actSchedule : ScheduleSwap → RelaxationRoundState → RelaxationRoundState
actSchedule identitySchedule s = s
actSchedule swapSchedule (relaxationRoundState r d false) =
  relaxationRoundState r d true
actSchedule swapSchedule (relaxationRoundState r d true) =
  relaxationRoundState r d false

record RelaxationScheduleConfluence : Set where
  constructor relaxationScheduleConfluence
  field
    scheduleSwapPreservesRoundObservation :
      (s : RelaxationRoundState) →
      observeRelaxation (actSchedule swapSchedule s) ≡ observeRelaxation s

canonicalToyScheduleConfluence : RelaxationScheduleConfluence
canonicalToyScheduleConfluence = relaxationScheduleConfluence (λ s → refl)

record BellmanFordFibreBoundary : Set where
  constructor bellmanFordFibreBoundary
  field
    scheduleCanBeResidualWithConfluenceWitness : Bool
    scheduleCanBeResidualWithConfluenceWitnessIsTrue :
      scheduleCanBeResidualWithConfluenceWitness ≡ true
    arbitraryInPlaceScheduleEquivalenceClaimed : Bool
    arbitraryInPlaceScheduleEquivalenceClaimedIsFalse :
      arbitraryInPlaceScheduleEquivalenceClaimed ≡ false
    negativeCycleDetectionErasedByQuotient : Bool
    negativeCycleDetectionErasedByQuotientIsFalse :
      negativeCycleDetectionErasedByQuotient ≡ false

canonicalBellmanFordFibreBoundary : BellmanFordFibreBoundary
canonicalBellmanFordFibreBoundary =
  bellmanFordFibreBoundary true refl false refl false refl
