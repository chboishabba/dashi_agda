module DASHI.Core.TemporalDiagnosisSalienceRecalibrationBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.TemporalDiagnosisFibreProjectionBidiExact as Temporal

------------------------------------------------------------------------
-- TEMPORAL SALIENCE RECALIBRATION
--
-- Salience is evaluated against the *current* diagnosis fibre rebuilt from
-- history.  Therefore the same debug observation can be inert while its target
-- diagnosis is already eliminated and become salient again after reactivation.
------------------------------------------------------------------------

frameCheckInertBeforeReactivation :
  Diagnosis.DiagnosisSalientOn
    Diagnosis.smallFrameCheck
    (Temporal.liveProjection Temporal.beforeReactivationBundle)
  → ⊥
frameCheckInertBeforeReactivation receipt with Diagnosis.eliminated receipt
... | Outcome.modelConflict , (before , notAfter) = notAfter before
... | Outcome.frameConflict , (before , notAfter) = Temporal.frameNotLiveBefore before
... | Outcome.premiseConflict , (before , notAfter) = notAfter before
... | Outcome.observationConflict , (() , _)
... | Outcome.ruleConflict , (() , _)
... | Outcome.consumerMismatch , (() , _)
... | Outcome.provenanceConflict , (() , _)
... | Outcome.authorityMismatch , (() , _)
... | Outcome.insufficientResolution , (() , _)

frameCheckSalientAfterReactivation :
  Diagnosis.DiagnosisSalientOn
    Diagnosis.smallFrameCheck
    (Temporal.liveProjection Temporal.afterReactivationBundle)
frameCheckSalientAfterReactivation =
  Diagnosis.strict-diagnosis-narrowing
    refine
    (Outcome.frameConflict , (Temporal.frameLiveAfter , (λ x → x)))
  where
    refine :
      ∀ diagnosis →
      Diagnosis.updateDiagnosisFibre Diagnosis.smallFrameCheck
        (Temporal.liveProjection Temporal.afterReactivationBundle)
        diagnosis →
      Temporal.liveProjection Temporal.afterReactivationBundle diagnosis
    refine Outcome.frameConflict ()
    refine diagnosis proof = proof

record TemporalSalienceChange : Set₁ where
  constructor temporal-salience-change
  field
    observation : Diagnosis.DebugObservation
    before : Diagnosis.DiagnosisFibre
    after : Diagnosis.DiagnosisFibre
    notSalientBefore : Diagnosis.DiagnosisSalientOn observation before → ⊥
    salientAfter : Diagnosis.DiagnosisSalientOn observation after

open TemporalSalienceChange public

frameCheckReactivatedSalience : TemporalSalienceChange
frameCheckReactivatedSalience =
  temporal-salience-change
    Diagnosis.smallFrameCheck
    (Temporal.liveProjection Temporal.beforeReactivationBundle)
    (Temporal.liveProjection Temporal.afterReactivationBundle)
    frameCheckInertBeforeReactivation
    frameCheckSalientAfterReactivation

data OnceInertAlwaysInert : Set where
data OnceEliminatedNeverReschedule : Set where
data SalienceMayIgnoreTemporalProjection : Set where

onceInertDoesNotMeanAlwaysInert : OnceInertAlwaysInert → ⊥
onceInertDoesNotMeanAlwaysInert ()

onceEliminatedDoesNotMeanNeverReschedule : OnceEliminatedNeverReschedule → ⊥
onceEliminatedDoesNotMeanNeverReschedule ()

salienceMustUseCurrentTemporalProjection : SalienceMayIgnoreTemporalProjection → ⊥
salienceMustUseCurrentTemporalProjection ()

record TemporalDiagnosisSalienceBoundary : Set where
  constructor temporal-diagnosis-salience-boundary
  field
    sameMoveMayChangeSalienceOverTime : Bool
    reactivationMayRescheduleOldDebugger : Bool
    historicalEliminationPermanentlySuppressesMove : Bool
    currentDiagnosisProjectionRequired : Bool

canonicalTemporalDiagnosisSalienceBoundary : TemporalDiagnosisSalienceBoundary
canonicalTemporalDiagnosisSalienceBoundary =
  temporal-diagnosis-salience-boundary true true false true
