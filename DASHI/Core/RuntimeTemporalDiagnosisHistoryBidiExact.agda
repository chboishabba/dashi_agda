module DASHI.Core.RuntimeTemporalDiagnosisHistoryBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.RuntimeDiagnosisRepairSchedulerBidiExact as Runtime
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.SequentialOutcomeBackpropagationBidiExact as Revision
import DASHI.Core.TemporalDiagnosisProvenanceHistoryBidiExact as Temporal
import DASHI.Core.TemporalDiagnosisSalienceRecalibrationBidiExact as Recalibration
import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.TemporalDiagnosisFibreProjectionBidiExact as Projection

------------------------------------------------------------------------
-- RUNTIME REPAIR WITH APPEND-ONLY DIAGNOSIS REACTIVATION
------------------------------------------------------------------------

reactivatedRuntimeFrameConflictRoutesToRechart :
  Runtime.runtimeRevision Outcome.frameConflict ≡ Revision.rechartRepresentation
reactivatedRuntimeFrameConflictRoutesToRechart =
  Runtime.runtimeFrameConflictRequestsRechart

priorRuntimeFrameEliminationStillAuditable :
  Temporal.TraceContains
    Temporal.frameEliminated
    Temporal.frameHistoryAfterReactivation
priorRuntimeFrameEliminationStillAuditable =
  Temporal.priorEliminationStillPresentAfterReactivation

frameControlMayBeRescheduledAfterRuntimeReactivation :
  Diagnosis.DiagnosisSalientOn
    Diagnosis.smallFrameCheck
    (Projection.liveProjection Projection.afterReactivationBundle)
frameControlMayBeRescheduledAfterRuntimeReactivation =
  Recalibration.frameCheckSalientAfterReactivation

data RuntimeReactivationRewritesEventHistory : Set where
data PriorRuntimeRepairBecomesRetroactivelyInvalid : Set where

runtimeReactivationDoesNotRewriteHistory :
  RuntimeReactivationRewritesEventHistory → ⊥
runtimeReactivationDoesNotRewriteHistory ()

priorRepairIsNotRetroactivelyInvalidated :
  PriorRuntimeRepairBecomesRetroactivelyInvalid → ⊥
priorRepairIsNotRetroactivelyInvalidated ()

record RuntimeTemporalDiagnosisBoundary : Set where
  constructor runtime-temporal-diagnosis-boundary
  field
    runtimeDiagnosisMayReactivate : Bool
    previousEliminationRemainsAuditable : Bool
    reactivationMayRescheduleDebugger : Bool
    reactivationRewritesRuntimeHistory : Bool

canonicalRuntimeTemporalDiagnosisBoundary : RuntimeTemporalDiagnosisBoundary
canonicalRuntimeTemporalDiagnosisBoundary =
  runtime-temporal-diagnosis-boundary true true true false
