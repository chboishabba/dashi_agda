module DASHI.Physics.Closure.W9CancellationPressureQcoreCompatibilityReceipt where

-- Planck/W9: typed check of the proposed weightedSupport/Qcore compatibility
-- identification.
--
-- The claim does not hold in the current repo types.  `weightedSupport` is a
-- Nat-valued upper bound for weighted max pressure over integer-pair inputs.
-- The W9 Qcore route requires an equality in ℤ between embedded cancellation
-- pressure and theorem-level contraction energy after canonical delta
-- transport.  The canonical 15 route already exports a counterexample to that
-- pressure witness, so this module records the mismatch and does not construct
-- a W9 kill receipt.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_)

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using (Int)

import DASHI.Arithmetic.MaxPressure as Max
import DASHI.Arithmetic.WeightedPressure as Weighted
import DASHI.Physics.Closure.BlockerKillConditions as Kill
import DASHI.Physics.Closure.CancellationPressureCompatibilityNextObligation as W9

data W9QcoreCompatibilityClaimStatus : Set where
  weightedSupportNotQcoreCompatibility :
    W9QcoreCompatibilityClaimStatus

WeightedSupportBoundType : Set
WeightedSupportBoundType =
  ∀ x y →
    Max.weightedMaxPressure x y ≤ Weighted.weightedSupport x y

Canonical15QcoreCompatibilityType : Setω
Canonical15QcoreCompatibilityType =
  W9.ExistingCancellationPressureCompatibilityObligation
    W9.canonical15Theorem
    W9.canonical15Dimension

record W9CancellationPressureQcoreCompatibilityDiagnostic : Setω where
  field
    weightedSupportBound :
      WeightedSupportBoundType

    canonical15ExistingRouteObstructed :
      Canonical15QcoreCompatibilityType → ⊥

    blockerKillCondition :
      Kill.KillCondition

    blockerKillConditionIsW9 :
      Kill.KillCondition.lane blockerKillCondition
      ≡
      Kill.W9Cancellation

    blockerKillConditionStillBlocked :
      Kill.KillCondition.currentState blockerKillCondition
      ≡
      Kill.blocked

    status :
      W9QcoreCompatibilityClaimStatus

    firstMissingType :
      String

    exactKillReceiptTypeName :
      String

    diagnosticBoundary :
      List String

canonicalW9CancellationPressureQcoreCompatibilityDiagnostic :
  W9CancellationPressureQcoreCompatibilityDiagnostic
canonicalW9CancellationPressureQcoreCompatibilityDiagnostic =
  record
    { weightedSupportBound =
        Max.weightedMaxPressure≤weightedSupport
    ; canonical15ExistingRouteObstructed =
        W9.canonical15ExistingPressureWitnessObstruction
    ; blockerKillCondition =
        Kill.w9KillCondition
    ; blockerKillConditionIsW9 =
        refl
    ; blockerKillConditionStillBlocked =
        refl
    ; status =
        weightedSupportNotQcoreCompatibility
    ; firstMissingType =
        "DASHI.Physics.Closure.CancellationPressureCompatibilityNextObligation.ExistingCancellationPressureCompatibilityObligation canonical15Theorem canonical15Dimension"
    ; exactKillReceiptTypeName =
        "DASHI.Physics.Closure.BlockerKillConditions.W9KillReceipt"
    ; diagnosticBoundary =
        "weightedSupport has type Int -> Int -> Nat and is used as an upper bound target"
        ∷ "weightedMaxPressure≤weightedSupport proves a Nat inequality, not a Qcore equality"
        ∷ "ExistingCancellationPressureCompatibilityObligation requires an ℤ equality to contractionEnergy after canonicalDeltaTransport"
        ∷ "canonical15ExistingPressureWitnessObstruction rejects that exact canonical-15 pressure witness"
        ∷ "BlockerKillConditions.W9KillReceipt is not constructed here"
        ∷ []
    }

currentW9QcoreCompatibilityClaimStatus :
  W9QcoreCompatibilityClaimStatus
currentW9QcoreCompatibilityClaimStatus =
  W9CancellationPressureQcoreCompatibilityDiagnostic.status
    canonicalW9CancellationPressureQcoreCompatibilityDiagnostic
