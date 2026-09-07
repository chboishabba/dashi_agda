module DASHI.Core.RuntimeDiagnosisRepairSchedulerBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.RuntimePluralEpistemicProgressBidiExact as Runtime
import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.SequentialOutcomeBackpropagationBidiExact as Revision

------------------------------------------------------------------------
-- RUNTIME / REPLAY <-> DIAGNOSIS-FIBRE REPAIR
------------------------------------------------------------------------

runtimeDiagnosisFibre : Diagnosis.DiagnosisFibre
runtimeDiagnosisFibre Outcome.observationConflict = ⊤
runtimeDiagnosisFibre Outcome.frameConflict = ⊤
runtimeDiagnosisFibre Outcome.modelConflict = ⊤
runtimeDiagnosisFibre Outcome.provenanceConflict = ⊤
runtimeDiagnosisFibre Outcome.insufficientResolution = ⊤
runtimeDiagnosisFibre _ = ⊥

runtimeRevision : Outcome.OutcomeDiagnosis → Revision.RevisionAction
runtimeRevision Outcome.observationConflict = Revision.reacquireObservation
runtimeRevision Outcome.frameConflict = Revision.rechartRepresentation
runtimeRevision Outcome.premiseConflict = Revision.inspectPremise
runtimeRevision Outcome.ruleConflict = Revision.inspectRule
runtimeRevision Outcome.modelConflict = Revision.reviseModel
runtimeRevision Outcome.consumerMismatch = Revision.reformulateConsumer
runtimeRevision Outcome.provenanceConflict = Revision.acquireIndependentProvenance
runtimeRevision Outcome.authorityMismatch = Revision.seekAuthorityReceipt
runtimeRevision Outcome.insufficientResolution = Revision.reacquireObservation

runtimeProvenanceConflictRequestsIndependentProvenance :
  runtimeRevision Outcome.provenanceConflict ≡ Revision.acquireIndependentProvenance
runtimeProvenanceConflictRequestsIndependentProvenance = refl

runtimeFrameConflictRequestsRechart :
  runtimeRevision Outcome.frameConflict ≡ Revision.rechartRepresentation
runtimeFrameConflictRequestsRechart = refl

runtimeResolutionConflictRequestsReacquisition :
  runtimeRevision Outcome.insufficientResolution ≡ Revision.reacquireObservation
runtimeResolutionConflictRequestsReacquisition = refl

runtimeAppendOnlyBoundary :
  Runtime.RuntimePluralEpistemicBoundary
runtimeAppendOnlyBoundary = Runtime.canonicalRuntimePluralEpistemicBoundary

data ReplayFailureMeansHistoryRewrite : Set where
data RepeatedRuntimeFailureIdentifiesUniqueCause : Set where

replayFailureDoesNotMeanHistoryRewrite : ReplayFailureMeansHistoryRewrite → ⊥
replayFailureDoesNotMeanHistoryRewrite ()

repeatedFailureNeedNotIdentifyUniqueCause :
  RepeatedRuntimeFailureIdentifiesUniqueCause → ⊥
repeatedFailureNeedNotIdentifyUniqueCause ()

record RuntimeDiagnosisSchedulerBoundary : Set where
  constructor runtime-diagnosis-scheduler-boundary
  field
    runtimeFailureMayHaveMultipleDiagnoses : Bool
    provenanceConflictRoutesToProvenanceRepair : Bool
    frameConflictRoutesToRechart : Bool
    lowResolutionRoutesToReacquisition : Bool
    replayFailureRewritesHistory : Bool

canonicalRuntimeDiagnosisSchedulerBoundary : RuntimeDiagnosisSchedulerBoundary
canonicalRuntimeDiagnosisSchedulerBoundary =
  runtime-diagnosis-scheduler-boundary true true true true false
