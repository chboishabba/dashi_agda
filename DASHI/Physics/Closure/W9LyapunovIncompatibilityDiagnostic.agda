module DASHI.Physics.Closure.W9LyapunovIncompatibilityDiagnostic where

-- W9 Planck lane: check whether the existing weighted max/support bound can
-- be consumed as the cancellation-pressure Lyapunov retarget consumer.
--
-- Result: the weighted-support bound is present and can inhabit the current
-- retarget consumer interface, but it is not the Lyapunov bridge.  A separate
-- narrow carryDepth+carryBudget Lyapunov adapter is constructible for
-- NormalizeAddState.  Neither receipt closes the dim-15 pressure/Qcore W9 gate.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_)

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using (Int)

import DASHI.Arithmetic.CancellationPressureCore as Core
import DASHI.Arithmetic.CancellationPressureLyapunovBridge as Lyapunov
import DASHI.Arithmetic.MaxPressure as Max
import DASHI.Arithmetic.WeightedPressure as Weighted
import DASHI.Physics.Closure.CancellationPressureCompatibilityNextObligation as W9
import DASHI.Physics.Closure.CancellationPressureRetargetConsumerObligation as W9f
import DASHI.Physics.Closure.CancellationPressureRetargetConsumerSourceDiagnostic as W9g
import DASHI.Physics.Closure.W9LyapunovAdapterReceipt as W9a
import DASHI.Physics.Closure.W9WeightedSupportRetargetConsumerReceipt as W9r

data W9LyapunovCompatibilityStatus : Set where
  weightedSupportBoundAvailable :
    W9LyapunovCompatibilityStatus
  weightedSupportRetargetAdapterAvailable :
    W9LyapunovCompatibilityStatus
  carryDepthBudgetLyapunovAdapterAvailable :
    W9LyapunovCompatibilityStatus
  dim15PressureQcoreCompatibilityStillMissing :
    W9LyapunovCompatibilityStatus

data W9WeightedSupportRetargetVerdict : Set where
  narrowAdaptersAvailableDim15CompatibilityStillMissing :
    W9WeightedSupportRetargetVerdict

record W9LyapunovIncompatibilityDiagnostic : Setω where
  field
    weightedSupportBound :
      ∀ x y →
        Max.weightedMaxPressure x y ≤ Weighted.weightedSupport x y

    retargetSourceDiagnostic :
      W9g.CancellationPressureRetargetConsumerSourceDiagnostic

    earlierRetargetConsumerInterfaceSourceWasMissing :
      W9g.CancellationPressureRetargetConsumerSourceDiagnostic.retargetConsumerInterfaceSource
        retargetSourceDiagnostic
      ≡
      W9g.sourceMissing

    earlierAcceptanceReceiptSourceWasMissing :
      W9g.CancellationPressureRetargetConsumerSourceDiagnostic.acceptanceReceiptSource
        retargetSourceDiagnostic
      ≡
      W9g.sourceMissing

    weightedSupportRetargetReceipt :
      W9r.WeightedSupportRetargetConsumerReceipt

    weightedSupportRetargetScope :
      W9r.WeightedSupportRetargetConsumerReceipt.receiptScope
        weightedSupportRetargetReceipt
      ≡
      W9r.retargetConsumerAcceptedOnly

    carryDepthBudgetLyapunovReceipt :
      W9a.W9LyapunovAdapterReceipt

    carryDepthBudgetLyapunovReceiptStatus :
      W9a.W9LyapunovAdapterReceipt.status
        carryDepthBudgetLyapunovReceipt
      ≡
      W9a.carryDepthBudgetBridgeConstructedNonPromoting

    currentClosureStatus :
      W9.W9Dim15ClosureStatus

    currentClosureStatusIsRetargetAwaitingConsumer :
      currentClosureStatus
      ≡
      W9.dim15RoutesExhaustedRetargetAwaitingConsumer

    weightedBoundStatus :
      W9LyapunovCompatibilityStatus

    lyapunovConsumerRequiredName :
      String

    retargetConsumerRequiredName :
      String

    retargetAcceptanceRequiredName :
      String

    lyapunovBridgeStillRequiredName :
      String

    firstRemainingMissingType :
      String

    verdict :
      W9WeightedSupportRetargetVerdict

    diagnosticBoundary :
      List String

    exactW9Status :
      List String

canonicalW9LyapunovIncompatibilityDiagnostic :
  W9LyapunovIncompatibilityDiagnostic
canonicalW9LyapunovIncompatibilityDiagnostic =
  record
    { weightedSupportBound =
        Max.weightedMaxPressure≤weightedSupport
    ; retargetSourceDiagnostic =
        W9g.currentCancellationPressureRetargetConsumerSourceDiagnostic
    ; earlierRetargetConsumerInterfaceSourceWasMissing =
        refl
    ; earlierAcceptanceReceiptSourceWasMissing =
        refl
    ; weightedSupportRetargetReceipt =
        W9r.canonicalWeightedSupportRetargetConsumerReceipt
    ; weightedSupportRetargetScope =
        refl
    ; carryDepthBudgetLyapunovReceipt =
        W9a.canonicalW9LyapunovAdapterReceipt
    ; carryDepthBudgetLyapunovReceiptStatus =
        refl
    ; currentClosureStatus =
        W9.Dim15DeltaToQuadraticClosureObstruction.closureStatus
          W9.canonical15DeltaToQuadraticClosureObstruction
    ; currentClosureStatusIsRetargetAwaitingConsumer =
        refl
    ; weightedBoundStatus =
        carryDepthBudgetLyapunovAdapterAvailable
    ; lyapunovConsumerRequiredName =
        "DASHI.Arithmetic.CancellationPressureLyapunovBridge.CancellationPressureLyapunovBridge"
    ; retargetConsumerRequiredName =
        "DASHI.Physics.Closure.CancellationPressureRetargetConsumerObligation.RetargetConsumerInterface"
    ; retargetAcceptanceRequiredName =
        "DASHI.Physics.Closure.CancellationPressureRetargetConsumerObligation.CancellationPressureRetargetConsumerAcceptanceReceipt"
    ; lyapunovBridgeStillRequiredName =
        "No longer missing for the narrow NormalizeAddState carryDepth+carryBudget adapter"
    ; firstRemainingMissingType =
        "DASHI.Physics.Closure.CancellationPressureCompatibilityNextObligation.ExistingCancellationPressureCompatibilityObligation canonical15Theorem canonical15Dimension"
    ; verdict =
        narrowAdaptersAvailableDim15CompatibilityStillMissing
    ; diagnosticBoundary =
        "weightedMaxPressure≤weightedSupport is available and validated"
        ∷ "That theorem is only a pressure upper bound over integer-pair inputs"
        ∷ "A narrow RetargetConsumerInterface adapter now consumes that bound for canonicalPairPressureRetargetReceipt"
        ∷ "The adapter is non-promoting and preserves the non-Qcore retarget boundary"
        ∷ "A separate carryDepth+carryBudget CancellationPressureLyapunovBridge is constructible for NormalizeAddState"
        ∷ "That Lyapunov adapter is not the dim-15 pair-pressure/Qcore compatibility route"
        ∷ "The first remaining theorem-facing type is ExistingCancellationPressureCompatibilityObligation for canonical15Theorem and canonical15Dimension"
        ∷ []
    ; exactW9Status =
        "W9 remains dim15RoutesExhaustedRetargetAwaitingConsumer"
        ∷ "A weighted-support RetargetConsumerInterface and acceptance receipt are constructed"
        ∷ "A narrow carryDepth+carryBudget CancellationPressureLyapunovBridge is constructed only for NormalizeAddState"
        ∷ "This diagnostic does not claim dim-15 quadratic forcing or W9 closure"
        ∷ []
    }

currentW9LyapunovVerdict :
  W9WeightedSupportRetargetVerdict
currentW9LyapunovVerdict =
  W9LyapunovIncompatibilityDiagnostic.verdict
    canonicalW9LyapunovIncompatibilityDiagnostic
