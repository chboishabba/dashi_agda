module DASHI.Computation.BMSSPTemporalRecursionDepthBudgetExact where

-- Finite recursion-depth/work-budget certificate for the BMSSP trajectory.
-- We keep the exact natural-number inequality l*t <= L instead of pretending
-- to own real logarithms or floor division.  This is the denominator-free
-- form of the paper-facing relation l <= L/t.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; _*_; _+_)
open import Data.Nat using (_≤_)

import DASHI.Computation.BMSSPPullPivotTemporalSameCarrierExact as Same
import DASHI.Computation.BMSSPTemporalOutcomeBoundExact as Outcome

------------------------------------------------------------------------
-- 1. Recursion depth is a property of one temporal search trajectory.
------------------------------------------------------------------------

record BMSSPRecursionDepthBudget
  (B : Same.BMSSPTemporalSameCarrier) : Set where
  constructor bmsspRecursionDepthBudget
  field
    recursionDepth : Nat
    tScale : Nat
    logBudget : Nat

    depthTimesScaleWithinLogBudget :
      recursionDepth * tScale ≤ logBudget

open BMSSPRecursionDepthBudget public

------------------------------------------------------------------------
-- 2. Per-trajectory finite work accounting.
------------------------------------------------------------------------

record BMSSPTemporalWorkBudget
  (B : Same.BMSSPTemporalSameCarrier)
  (O : Outcome.BMSSPTemporalOutcomeContract B) : Set where
  constructor bmsspTemporalWorkBudget
  field
    pullCharge : Nat → Nat
    pivotCharge : Nat → Nat
    recursiveCharge : Nat → Nat

    stageCharge : Nat → Nat
    stageChargeExact :
      (t : Nat) →
      stageCharge t ≡
      pullCharge t + pivotCharge t + recursiveCharge t

    stageChargeWithinObservedWorkload :
      (t : Nat) →
      stageCharge t ≤ Outcome.workloadAt O t

open BMSSPTemporalWorkBudget public

------------------------------------------------------------------------
-- 3. The pivot-compression receipt remains available at every time slice.
------------------------------------------------------------------------

temporalPivotCompression :
  (B : Same.BMSSPTemporalSameCarrier) →
  (t : Nat) →
  let layer = Same.pivotLayer B t in
  Same.k layer * Same.pivotCount layer ≤ Same.workCount layer
temporalPivotCompression B t = Same.currentPivotCompression B t

------------------------------------------------------------------------
-- 4. Boundary: finite arithmetic first, asymptotics later.
------------------------------------------------------------------------

record BMSSPRecursionBudgetBoundary : Set where
  constructor bmsspRecursionBudgetBoundary
  field
    recursionDepthAttachedToSameTrajectory : Bool
    recursionDepthAttachedToSameTrajectoryIsTrue :
      recursionDepthAttachedToSameTrajectory ≡ true

    denominatorFreeDepthBoundOwned : Bool
    denominatorFreeDepthBoundOwnedIsTrue :
      denominatorFreeDepthBoundOwned ≡ true

    realLogDivisionTheoremClaimed : Bool
    realLogDivisionTheoremClaimedIsFalse :
      realLogDivisionTheoremClaimed ≡ false

    bigO2025BoundClaimedHere : Bool
    bigO2025BoundClaimedHereIsFalse :
      bigO2025BoundClaimedHere ≡ false

canonicalBMSSPRecursionBudgetBoundary : BMSSPRecursionBudgetBoundary
canonicalBMSSPRecursionBudgetBoundary =
  bmsspRecursionBudgetBoundary true refl true refl false refl false refl
