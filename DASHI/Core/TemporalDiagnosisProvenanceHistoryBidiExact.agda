module DASHI.Core.TemporalDiagnosisProvenanceHistoryBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.DiagnosisExperimentPortfolioBidiExact as Portfolio
import DASHI.Core.AppendOnlyEvidenceResidualRevisionExact as AppendOnly

------------------------------------------------------------------------
-- TEMPORAL / PROVENANCE-BEARING DIAGNOSIS HISTORY
--
-- A diagnosis is not represented only by its current live/dead bit.  Every
-- activation, elimination and reactivation is an append-only event carrying
-- its time, a typed result/debug-move trigger, and provenance rationale.
------------------------------------------------------------------------

data DiagnosisTransition : Set where
  activated eliminated reactivated : DiagnosisTransition

data CurrentDiagnosisStatus : Set where
  currentlyLive currentlyEliminated : CurrentDiagnosisStatus

data DiagnosisEventTrigger : Set where
  resultTrigger : Outcome.ExperimentalOutcome → DiagnosisEventTrigger
  debugMoveTrigger : Portfolio.DebugMoveKind → DiagnosisEventTrigger

record DiagnosisEvent (diagnosis : Outcome.OutcomeDiagnosis) : Set where
  constructor diagnosis-event
  field
    transition : DiagnosisTransition
    time : Nat
    trigger : DiagnosisEventTrigger
    triggerReference : String
    rationaleReference : String
    provenanceReference : String

open DiagnosisEvent public

DiagnosisTrace : Outcome.OutcomeDiagnosis → Set
DiagnosisTrace diagnosis = List (DiagnosisEvent diagnosis)

extendTrace :
  ∀ {diagnosis} →
  DiagnosisEvent diagnosis → DiagnosisTrace diagnosis → DiagnosisTrace diagnosis
extendTrace event history = event ∷ history

data TraceContains {diagnosis : Outcome.OutcomeDiagnosis}
    (event : DiagnosisEvent diagnosis) :
    DiagnosisTrace diagnosis → Set where
  here : ∀ {rest} → TraceContains event (event ∷ rest)
  there : ∀ {head rest} →
    TraceContains event rest →
    TraceContains event (head ∷ rest)

oldDiagnosisEventPersistsAfterExtension :
  ∀ {diagnosis}
    {old new : DiagnosisEvent diagnosis}
    {history : DiagnosisTrace diagnosis} →
  TraceContains old history →
  TraceContains old (extendTrace new history)
oldDiagnosisEventPersistsAfterExtension receipt = there receipt

currentStatus :
  ∀ {diagnosis} → DiagnosisTrace diagnosis → CurrentDiagnosisStatus
currentStatus [] = currentlyEliminated
currentStatus (event ∷ rest) with transition event
... | activated = currentlyLive
... | eliminated = currentlyEliminated
... | reactivated = currentlyLive

------------------------------------------------------------------------
-- Exact frame-conflict trace: live -> eliminated -> reactivated.
------------------------------------------------------------------------

frameActivated : DiagnosisEvent Outcome.frameConflict
frameActivated =
  diagnosis-event activated 1
    (resultTrigger Outcome.adverse)
    "initial adverse result activates a live frame-conflict diagnosis"
    "frame conflict remains compatible with the initial result"
    "initial diagnosis-fibre construction receipt"

frameEliminated : DiagnosisEvent Outcome.frameConflict
frameEliminated =
  diagnosis-event eliminated 2
    (debugMoveTrigger Portfolio.frameControl)
    "frame-control debugging move"
    "frame control makes frame conflict incompatible with the then-current debugging observation"
    "diagnosis narrowing receipt"

frameReactivated : DiagnosisEvent Outcome.frameConflict
frameReactivated =
  diagnosis-event reactivated 3
    (resultTrigger Outcome.indeterminate)
    "later indeterminate result under changed representation/context"
    "new evidence makes frame conflict compatible again without deleting its prior elimination"
    "append-only reactivation receipt"

frameActivationWasResultTriggered :
  trigger frameActivated ≡ resultTrigger Outcome.adverse
frameActivationWasResultTriggered = refl

frameEliminationWasDebugMoveTriggered :
  trigger frameEliminated ≡ debugMoveTrigger Portfolio.frameControl
frameEliminationWasDebugMoveTriggered = refl

frameReactivationWasLaterResultTriggered :
  trigger frameReactivated ≡ resultTrigger Outcome.indeterminate
frameReactivationWasLaterResultTriggered = refl

frameHistoryAtActivation : DiagnosisTrace Outcome.frameConflict
frameHistoryAtActivation = frameActivated ∷ []

frameHistoryAfterElimination : DiagnosisTrace Outcome.frameConflict
frameHistoryAfterElimination = frameEliminated ∷ frameHistoryAtActivation

frameHistoryAfterReactivation : DiagnosisTrace Outcome.frameConflict
frameHistoryAfterReactivation = frameReactivated ∷ frameHistoryAfterElimination

frameInitiallyLive :
  currentStatus frameHistoryAtActivation ≡ currentlyLive
frameInitiallyLive = refl

frameThenEliminated :
  currentStatus frameHistoryAfterElimination ≡ currentlyEliminated
frameThenEliminated = refl

frameLaterReactivated :
  currentStatus frameHistoryAfterReactivation ≡ currentlyLive
frameLaterReactivated = refl

priorEliminationStillPresentAfterReactivation :
  TraceContains frameEliminated frameHistoryAfterReactivation
priorEliminationStillPresentAfterReactivation = there here

priorActivationStillPresentAfterReactivation :
  TraceContains frameActivated frameHistoryAfterReactivation
priorActivationStillPresentAfterReactivation = there (there here)

------------------------------------------------------------------------
-- Existing append-only evidence donor remains the governing non-monotonicity
-- law: preserved evidence/history does not force monotone current conclusions.
------------------------------------------------------------------------

appendOnlyEvidenceMayReopenPreviouslyAcceptedCarrier :
  AppendOnly.AppendOnlyEvidenceRevisionBoundary.newEvidenceMayReopenPreviouslyAcceptedCarrier
    AppendOnly.canonicalAppendOnlyEvidenceRevisionBoundary
  ≡ true
appendOnlyEvidenceMayReopenPreviouslyAcceptedCarrier = refl

appendOnlyEvidenceDoesNotRequireMonotoneResidualAction :
  AppendOnly.AppendOnlyEvidenceRevisionBoundary.appendOnlyEvidenceImpliesMonotoneResidualAction
    AppendOnly.canonicalAppendOnlyEvidenceRevisionBoundary
  ≡ false
appendOnlyEvidenceDoesNotRequireMonotoneResidualAction = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ReactivationDeletesElimination : Set where
data EliminatedOnceMeansForeverFalse : Set where
data ReactivatedMeansPreviouslyEliminatedWasWrong : Set where
data CurrentStatusErasesHistory : Set where

data TriggerReferenceCreatesWorldTruth : Set where

reactivationDoesNotDeleteElimination : ReactivationDeletesElimination → ⊥
reactivationDoesNotDeleteElimination ()

eliminatedOnceDoesNotMeanForeverFalse : EliminatedOnceMeansForeverFalse → ⊥
eliminatedOnceDoesNotMeanForeverFalse ()

reactivationDoesNotRetroactivelyRefutePriorElimination :
  ReactivatedMeansPreviouslyEliminatedWasWrong → ⊥
reactivationDoesNotRetroactivelyRefutePriorElimination ()

currentProjectionDoesNotEraseDiagnosisHistory : CurrentStatusErasesHistory → ⊥
currentProjectionDoesNotEraseDiagnosisHistory ()

typedTriggerDoesNotCreateWorldTruth : TriggerReferenceCreatesWorldTruth → ⊥
typedTriggerDoesNotCreateWorldTruth ()

record TemporalDiagnosisHistoryBoundary : Set where
  constructor temporal-diagnosis-history-boundary
  field
    historyAppendOnly : Bool
    currentStatusMayBeNonMonotone : Bool
    eliminatedDiagnosisMayReactivate : Bool
    eventTriggerIsTyped : Bool
    reactivationDeletesPriorElimination : Bool
    currentStatusIsWholeHistory : Bool

canonicalTemporalDiagnosisHistoryBoundary : TemporalDiagnosisHistoryBoundary
canonicalTemporalDiagnosisHistoryBoundary =
  temporal-diagnosis-history-boundary true true true true false false
