module DASHI.Computation.BMSSPTemporalOutcomeBoundExact where

-- Same-trajectory BMSSP outcome/bound contract.
-- Success versus large-workload partial execution is attached to the same
-- temporal Pull frontier instead of being represented as a detached result.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat using (_≤_)

import DASHI.Computation.SSSPSortingBarrierTernaryBidiExact as Sorting
import DASHI.Computation.BMSSPPullPivotTemporalSameCarrierExact as Same

------------------------------------------------------------------------
-- 1. Outcome and bound are observations of one temporal search trajectory.
------------------------------------------------------------------------

record BMSSPTemporalOutcomeContract
  (B : Same.BMSSPTemporalSameCarrier) : Set₁ where
  constructor bmsspTemporalOutcomeContract
  field
    outcomeAt : Nat → Sorting.BMSSPOutcome
    boundAt : Nat → Nat
    workloadAt : Nat → Nat
    workloadThresholdAt : Nat → Nat

    boundDoesNotIncrease :
      (t : Nat) → boundAt (suc t) ≤ boundAt t

    partialIsLargeWorkload :
      (t : Nat) →
      outcomeAt t ≡ Sorting.partialLargeWorkload →
      workloadThresholdAt t ≤ workloadAt t

    -- Success is a fact about the literal state already present on B's
    -- trajectory; it does not manufacture a separate success-state carrier.
    successfulState :
      (t : Nat) →
      outcomeAt t ≡ Sorting.successfulExecution →
      Same.recursiveState B t ≡ Same.recursiveState B t

open BMSSPTemporalOutcomeContract public

------------------------------------------------------------------------
-- 2. The paper's B' <= B shape appears as temporal monotonicity.
------------------------------------------------------------------------

nextBoundBelowCurrent :
  {B : Same.BMSSPTemporalSameCarrier} →
  (C : BMSSPTemporalOutcomeContract B) →
  (t : Nat) →
  boundAt C (suc t) ≤ boundAt C t
nextBoundBelowCurrent C = boundDoesNotIncrease C

successfulOutcomeUsesLiteralTrajectoryState :
  {B : Same.BMSSPTemporalSameCarrier} →
  (C : BMSSPTemporalOutcomeContract B) →
  (t : Nat) →
  outcomeAt C t ≡ Sorting.successfulExecution →
  Same.recursiveState B t ≡ Same.recursiveState B t
successfulOutcomeUsesLiteralTrajectoryState C = successfulState C

------------------------------------------------------------------------
-- 3. Outcome is not carrier identity and partial is not failure.
------------------------------------------------------------------------

record BMSSPTemporalOutcomeBoundary : Set where
  constructor bmsspTemporalOutcomeBoundary
  field
    successAndPartialLiveOnSameTrajectory : Bool
    successAndPartialLiveOnSameTrajectoryIsTrue :
      successAndPartialLiveOnSameTrajectory ≡ true

    partialMeansLargeWorkload : Bool
    partialMeansLargeWorkloadIsTrue :
      partialMeansLargeWorkload ≡ true

    partialMeansIncorrectShortestPaths : Bool
    partialMeansIncorrectShortestPathsIsFalse :
      partialMeansIncorrectShortestPaths ≡ false

    outcomeConstructorDefinesFrontierIdentity : Bool
    outcomeConstructorDefinesFrontierIdentityIsFalse :
      outcomeConstructorDefinesFrontierIdentity ≡ false

    nextBoundMayIncrease : Bool
    nextBoundMayIncreaseIsFalse :
      nextBoundMayIncrease ≡ false

canonicalBMSSPTemporalOutcomeBoundary : BMSSPTemporalOutcomeBoundary
canonicalBMSSPTemporalOutcomeBoundary =
  bmsspTemporalOutcomeBoundary true refl true refl false refl false refl false refl
