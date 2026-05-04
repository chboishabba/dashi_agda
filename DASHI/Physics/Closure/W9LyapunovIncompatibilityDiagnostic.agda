module DASHI.Physics.Closure.W9LyapunovIncompatibilityDiagnostic where

-- W9 Planck lane: check whether the existing weighted max/support bound can
-- be consumed as the cancellation-pressure Lyapunov retarget consumer.
--
-- Result: the bound is present, but it is not a consumer for the current
-- interfaces.  It proves a Nat inequality over integer-pair pressure, while
-- the Lyapunov side requires a CancellationPressureLyapunovBridge and the
-- retarget side requires a RetargetConsumerInterface plus acceptance receipt.
-- This diagnostic is intentionally non-promoting.

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

data W9LyapunovCompatibilityStatus : Set where
  weightedSupportBoundAvailable :
    W9LyapunovCompatibilityStatus
  weightedSupportNotALyapunovConsumer :
    W9LyapunovCompatibilityStatus

data W9WeightedSupportRetargetVerdict : Set where
  typedIncompatibilityDiagnostic :
    W9WeightedSupportRetargetVerdict

record W9LyapunovIncompatibilityDiagnostic : Setω where
  field
    weightedSupportBound :
      ∀ x y →
        Max.weightedMaxPressure x y ≤ Weighted.weightedSupport x y

    retargetSourceDiagnostic :
      W9g.CancellationPressureRetargetConsumerSourceDiagnostic

    retargetConsumerInterfaceSourceIsMissing :
      W9g.CancellationPressureRetargetConsumerSourceDiagnostic.retargetConsumerInterfaceSource
        retargetSourceDiagnostic
      ≡
      W9g.sourceMissing

    acceptanceReceiptSourceIsMissing :
      W9g.CancellationPressureRetargetConsumerSourceDiagnostic.acceptanceReceiptSource
        retargetSourceDiagnostic
      ≡
      W9g.sourceMissing

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
    ; retargetConsumerInterfaceSourceIsMissing =
        refl
    ; acceptanceReceiptSourceIsMissing =
        refl
    ; currentClosureStatus =
        W9.Dim15DeltaToQuadraticClosureObstruction.closureStatus
          W9.canonical15DeltaToQuadraticClosureObstruction
    ; currentClosureStatusIsRetargetAwaitingConsumer =
        refl
    ; weightedBoundStatus =
        weightedSupportNotALyapunovConsumer
    ; lyapunovConsumerRequiredName =
        "DASHI.Arithmetic.CancellationPressureLyapunovBridge.CancellationPressureLyapunovBridge"
    ; retargetConsumerRequiredName =
        "DASHI.Physics.Closure.CancellationPressureRetargetConsumerObligation.RetargetConsumerInterface"
    ; retargetAcceptanceRequiredName =
        "DASHI.Physics.Closure.CancellationPressureRetargetConsumerObligation.CancellationPressureRetargetConsumerAcceptanceReceipt"
    ; verdict =
        typedIncompatibilityDiagnostic
    ; diagnosticBoundary =
        "weightedMaxPressure≤weightedSupport is available and validated"
        ∷ "That theorem is only a pressure upper bound over integer-pair inputs"
        ∷ "CancellationPressureLyapunovBridge requires a CancellationPressureMDL bridge plus MDLLyapunov"
        ∷ "CancellationPressureRetargetConsumerAcceptanceReceipt requires a concrete RetargetConsumerInterface"
        ∷ "No current interface consumes weightedMaxPressure≤weightedSupport as the missing retarget acceptance receipt"
        ∷ []
    ; exactW9Status =
        "W9 remains retarget-awaiting-consumer"
        ∷ "This diagnostic does not construct a RetargetConsumerInterface"
        ∷ "This diagnostic does not construct a CancellationPressureRetargetConsumerAcceptanceReceipt"
        ∷ "This diagnostic does not claim dim-15 quadratic forcing or W9 closure"
        ∷ []
    }

currentW9LyapunovVerdict :
  W9WeightedSupportRetargetVerdict
currentW9LyapunovVerdict =
  W9LyapunovIncompatibilityDiagnostic.verdict
    canonicalW9LyapunovIncompatibilityDiagnostic
