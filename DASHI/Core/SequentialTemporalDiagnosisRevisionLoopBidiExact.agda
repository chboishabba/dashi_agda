module DASHI.Core.SequentialTemporalDiagnosisRevisionLoopBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.SequentialDiagnosisDebugLoopBidiExact as Sequential
import DASHI.Core.TemporalDiagnosisProvenanceHistoryBidiExact as Temporal
import DASHI.Core.TemporalDiagnosisFibreProjectionBidiExact as Projection
import DASHI.Core.TemporalDiagnosisSalienceRecalibrationBidiExact as Recalibration

------------------------------------------------------------------------
-- SEQUENTIAL TEMPORAL DIAGNOSIS LOOP
--
-- A diagnosis previously eliminated by a debug move may reactivate after later
-- evidence.  Rebuild the current fibre from append-only history, recompute
-- salience, and reschedule debugging without automatically reopening an
-- unaffected terminal consumer.
------------------------------------------------------------------------

record TemporalDebugCycle : Set₁ where
  constructor temporal-debug-cycle
  field
    beforeHistory : Projection.DiagnosisHistoryBundle
    afterHistory : Projection.DiagnosisHistoryBundle
    reactivatedDiagnosis : Outcome.OutcomeDiagnosis
    wasNotLiveBefore : Projection.liveProjection beforeHistory reactivatedDiagnosis → ⊥
    isLiveAfter : Projection.liveProjection afterHistory reactivatedDiagnosis
    historicalEliminationRetained :
      Temporal.TraceContains
        Temporal.frameEliminated
        Temporal.frameHistoryAfterReactivation
    rescheduledObservation : Diagnosis.DebugObservation
    observationSalientAfter :
      Diagnosis.DiagnosisSalientOn
        rescheduledObservation
        (Projection.liveProjection afterHistory)

open TemporalDebugCycle public

canonicalTemporalDebugCycle : TemporalDebugCycle
canonicalTemporalDebugCycle =
  temporal-debug-cycle
    Projection.beforeReactivationBundle
    Projection.afterReactivationBundle
    Outcome.frameConflict
    Projection.frameNotLiveBefore
    Projection.frameLiveAfter
    Temporal.priorEliminationStillPresentAfterReactivation
    Diagnosis.smallFrameCheck
    Recalibration.frameCheckSalientAfterReactivation

frameWasEliminatedBeforeCycle :
  wasNotLiveBefore canonicalTemporalDebugCycle
  ≡ Projection.frameNotLiveBefore
frameWasEliminatedBeforeCycle = refl

frameIsLiveAfterCycle :
  isLiveAfter canonicalTemporalDebugCycle
frameIsLiveAfterCycle = Projection.frameLiveAfter

rescheduledFrameControlIsSalient :
  Diagnosis.DiagnosisSalientOn
    (rescheduledObservation canonicalTemporalDebugCycle)
    (Projection.liveProjection (afterHistory canonicalTemporalDebugCycle))
rescheduledFrameControlIsSalient =
  observationSalientAfter canonicalTemporalDebugCycle

------------------------------------------------------------------------
-- Existing decision closure and temporal explanatory reopening coexist.
------------------------------------------------------------------------

data ReactivationMustImmediatelyReopenConsumer : Set where
data HistoricalEliminationBlocksRescheduling : Set where
data ReschedulingDeletesPriorDebugReceipt : Set where

reactivationNeedNotImmediatelyReopenConsumer :
  ReactivationMustImmediatelyReopenConsumer → ⊥
reactivationNeedNotImmediatelyReopenConsumer ()

historicalEliminationDoesNotBlockRescheduling :
  HistoricalEliminationBlocksRescheduling → ⊥
historicalEliminationDoesNotBlockRescheduling ()

reschedulingDoesNotDeletePriorDebugReceipt :
  ReschedulingDeletesPriorDebugReceipt → ⊥
reschedulingDoesNotDeletePriorDebugReceipt ()

sequentialDebuggerAlreadyAllowsConsumerToRemainClosed :
  Sequential.SequentialDiagnosisLoopBoundary.debugObservationMustImmediatelyReopenConsumer
    Sequential.canonicalSequentialDiagnosisLoopBoundary
  ≡ false
sequentialDebuggerAlreadyAllowsConsumerToRemainClosed = refl

record SequentialTemporalDiagnosisBoundary : Set where
  constructor sequential-temporal-diagnosis-boundary
  field
    eliminatedDiagnosisMayReactivate : Bool
    currentFibreRebuiltBeforeScheduling : Bool
    oldDebuggerMayBeRescheduled : Bool
    priorEliminationReceiptRetained : Bool
    reactivationAutomaticallyReopensConsumer : Bool

canonicalSequentialTemporalDiagnosisBoundary : SequentialTemporalDiagnosisBoundary
canonicalSequentialTemporalDiagnosisBoundary =
  sequential-temporal-diagnosis-boundary true true true true false
