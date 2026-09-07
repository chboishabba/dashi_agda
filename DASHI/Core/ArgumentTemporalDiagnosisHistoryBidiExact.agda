module DASHI.Core.ArgumentTemporalDiagnosisHistoryBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.ArgumentDiagnosisDebuggingBidiExact as Argument
import DASHI.Core.ArgumentResponseNonGeometricOppositeBidiExact as Response
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.TemporalDiagnosisProvenanceHistoryBidiExact as Temporal
import DASHI.Core.TemporalDiagnosisSalienceRecalibrationBidiExact as Recalibration
import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.TemporalDiagnosisFibreProjectionBidiExact as Projection

------------------------------------------------------------------------
-- ARGUMENT DEBUGGING WITH TEMPORAL DIAGNOSIS HISTORY
------------------------------------------------------------------------

reactivatedFrameDiagnosisStillTargetsFrameInspection :
  Argument.responseDiagnosis Response.disputeCharacterisation
  ≡ Outcome.frameConflict
reactivatedFrameDiagnosisStillTargetsFrameInspection = refl

priorFrameEliminationRemainsInArgumentHistory :
  Temporal.TraceContains
    Temporal.frameEliminated
    Temporal.frameHistoryAfterReactivation
priorFrameEliminationRemainsInArgumentHistory =
  Temporal.priorEliminationStillPresentAfterReactivation

frameDebuggerMayBecomeSalientAgain :
  Diagnosis.DiagnosisSalientOn
    Diagnosis.smallFrameCheck
    (Projection.liveProjection Projection.afterReactivationBundle)
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
