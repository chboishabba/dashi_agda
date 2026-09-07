module DASHI.Core.TemporalDiagnosisFibreProjectionBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.TemporalDiagnosisProvenanceHistoryBidiExact as Temporal

------------------------------------------------------------------------
-- CURRENT DIAGNOSIS FIBRE AS A PROJECTION OF APPEND-ONLY DIAGNOSIS HISTORY
------------------------------------------------------------------------

record DiagnosisHistoryBundle : Set₁ where
  constructor diagnosis-history-bundle
  field
    traceFor :
      (diagnosis : Outcome.OutcomeDiagnosis) →
      Temporal.DiagnosisTrace diagnosis

open DiagnosisHistoryBundle public

liveProjection : DiagnosisHistoryBundle → Diagnosis.DiagnosisFibre
liveProjection bundle diagnosis =
  Temporal.currentStatus (traceFor bundle diagnosis) ≡ Temporal.currentlyLive

------------------------------------------------------------------------
-- Exact histories before and after a frame-conflict reactivation.
------------------------------------------------------------------------

modelActivated : Temporal.DiagnosisEvent Outcome.modelConflict
modelActivated =
  Temporal.diagnosis-event Temporal.activated 1
    "initial result" "none"
    "model conflict remains live"
    "model diagnosis provenance"

premiseActivated : Temporal.DiagnosisEvent Outcome.premiseConflict
premiseActivated =
  Temporal.diagnosis-event Temporal.activated 1
    "initial result" "none"
    "premise conflict remains live"
    "premise diagnosis provenance"

emptyTrace :
  (diagnosis : Outcome.OutcomeDiagnosis) →
  Temporal.DiagnosisTrace diagnosis
emptyTrace diagnosis = []

beforeReactivationBundle : DiagnosisHistoryBundle
beforeReactivationBundle =
  diagnosis-history-bundle traces
  where
    traces :
      (diagnosis : Outcome.OutcomeDiagnosis) →
      Temporal.DiagnosisTrace diagnosis
    traces Outcome.modelConflict = modelActivated ∷ []
    traces Outcome.frameConflict = Temporal.frameHistoryAfterElimination
    traces Outcome.premiseConflict = premiseActivated ∷ []
    traces diagnosis = []

afterReactivationBundle : DiagnosisHistoryBundle
afterReactivationBundle =
  diagnosis-history-bundle traces
  where
    traces :
      (diagnosis : Outcome.OutcomeDiagnosis) →
      Temporal.DiagnosisTrace diagnosis
    traces Outcome.modelConflict = modelActivated ∷ []
    traces Outcome.frameConflict = Temporal.frameHistoryAfterReactivation
    traces Outcome.premiseConflict = premiseActivated ∷ []
    traces diagnosis = []

modelLiveBefore : liveProjection beforeReactivationBundle Outcome.modelConflict
modelLiveBefore = refl

premiseLiveBefore : liveProjection beforeReactivationBundle Outcome.premiseConflict
premiseLiveBefore = refl

frameNotLiveBefore :
  liveProjection beforeReactivationBundle Outcome.frameConflict → ⊥
frameNotLiveBefore ()

frameLiveAfter : liveProjection afterReactivationBundle Outcome.frameConflict
frameLiveAfter = refl

modelStillLiveAfter : liveProjection afterReactivationBundle Outcome.modelConflict
modelStillLiveAfter = refl

premiseStillLiveAfter : liveProjection afterReactivationBundle Outcome.premiseConflict
premiseStillLiveAfter = refl

------------------------------------------------------------------------
-- Reactivation can enlarge the *current* fibre even though history only grows.
------------------------------------------------------------------------

record StrictCurrentFibreExpansion
    (before after : Diagnosis.DiagnosisFibre) : Set where
  constructor strict-current-fibre-expansion
  field
    preservesOldLive : ∀ diagnosis → before diagnosis → after diagnosis
    newlyLive :
      Σ Outcome.OutcomeDiagnosis
        (λ diagnosis → after diagnosis × ¬ (before diagnosis))

open StrictCurrentFibreExpansion public

reactivationStrictlyExpandsCurrentDiagnosisFibre :
  StrictCurrentFibreExpansion
    (liveProjection beforeReactivationBundle)
    (liveProjection afterReactivationBundle)
reactivationStrictlyExpandsCurrentDiagnosisFibre =
  strict-current-fibre-expansion preserves
    (Outcome.frameConflict , (frameLiveAfter , frameNotLiveBefore))
  where
    preserves :
      ∀ diagnosis →
      liveProjection beforeReactivationBundle diagnosis →
      liveProjection afterReactivationBundle diagnosis
    preserves Outcome.modelConflict proof = proof
    preserves Outcome.frameConflict ()
    preserves Outcome.premiseConflict proof = proof
    preserves Outcome.observationConflict ()
    preserves Outcome.ruleConflict ()
    preserves Outcome.consumerMismatch ()
    preserves Outcome.provenanceConflict ()
    preserves Outcome.authorityMismatch ()
    preserves Outcome.insufficientResolution ()

------------------------------------------------------------------------
-- Thus a prior debugging posterior is only current-state information; it is
-- not an eternal theorem that eliminated diagnoses can never return.
------------------------------------------------------------------------

data PosteriorDiagnosisFibreIsForeverMonotone : Set where
data HistoricalEliminationForbidsFutureReactivation : Set where

temporalDiagnosisFibreNeedNotBeMonotoneNarrowing :
  PosteriorDiagnosisFibreIsForeverMonotone → ⊥
temporalDiagnosisFibreNeedNotBeMonotoneNarrowing ()

historicalEliminationDoesNotForbidFutureReactivation :
  HistoricalEliminationForbidsFutureReactivation → ⊥
historicalEliminationDoesNotForbidFutureReactivation ()

record TemporalDiagnosisProjectionBoundary : Set where
  constructor temporal-diagnosis-projection-boundary
  field
    currentFibreDerivedFromHistory : Bool
    appendOnlyHistoryMayProjectToExpandedCurrentFibre : Bool
    priorEliminationMeansNeverLiveAgain : Bool
    schedulerMustUseCurrentProjection : Bool

canonicalTemporalDiagnosisProjectionBoundary : TemporalDiagnosisProjectionBoundary
canonicalTemporalDiagnosisProjectionBoundary =
  temporal-diagnosis-projection-boundary true true false true
