module DASHI.Core.ArgumentTemporalDiagnosisHistoryBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.ArgumentDiagnosisDebuggingBidiExact as Argument
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.TemporalDiagnosisProvenanceHistoryBidiExact as Temporal
import DASHI.Core.TemporalDiagnosisSalienceRecalibrationBidiExact as Recalibration

------------------------------------------------------------------------
-- ARGUMENT DEBUGGING WITH TEMPORAL DIAGNOSIS HISTORY
------------------------------------------------------------------------

reactivatedFrameDiagnosisStillTargetsFrameInspection :
  Argument.responseDiagnosis DASHI.Core.ArgumentResponseNonGeometricOppositeBidiExact.disputeCharacterisation
  ≡ Outcome.frameConflict
reactivatedFrameDiagnosisStillTargetsFrameInspection = refl

priorFrameEliminationRemainsInArgumentHistory :
  Temporal.TraceContains
    Temporal.frameEliminated
    Temporal.frameHistoryAfterReactivation
priorFrameEliminationRemainsInArgumentHistory =
  Temporal.priorEliminationStillPresentAfterReactivation

frameDebuggerMayBecomeSalientAgain :
  DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact.DiagnosisSalientOn
    DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact.smallFrameCheck
    (DASHI.Core.TemporalDiagnosisFibreProjectionBidiExact.liveProjection
      DASHI.Core.TemporalDiagnosisFibreProjectionBidiExact.afterReactivationBundle)
frameDebuggerMayBecomeSalientAgain =
  Recalibration.frameCheckSalientAfterReactivation

data ReactivatedArgumentDiagnosisRefutesConclusion : Set where
data LaterReactivationErasesEarlierCounterargumentAudit : Set where

reactivatedDiagnosisDoesNotRefuteConclusion :
  ReactivatedArgumentDiagnosisRefutesConclusion → ⊥
reactivatedDiagnosisDoesNotRefuteConclusion ()

laterReactivationDoesNotEraseEarlierAudit :
  LaterReactivationErasesEarlierCounterargumentAudit → ⊥
laterReactivationDoesNotEraseEarlierAudit ()

record ArgumentTemporalDiagnosisBoundary : Set where
  constructor argument-temporal-diagnosis-boundary
  field
    diagnosisMayReactivateAfterEarlierElimination : Bool
    previousEliminationRemainsAuditable : Bool
    oldDebuggerMayBecomeSalientAgain : Bool
    reactivationEqualsConclusionRefutation : Bool

canonicalArgumentTemporalDiagnosisBoundary : ArgumentTemporalDiagnosisBoundary
canonicalArgumentTemporalDiagnosisBoundary =
  argument-temporal-diagnosis-boundary true true true false
