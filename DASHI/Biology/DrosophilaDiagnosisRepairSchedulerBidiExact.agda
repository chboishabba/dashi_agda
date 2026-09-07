module DASHI.Biology.DrosophilaDiagnosisRepairSchedulerBidiExact where

open import DASHI.Core.Prelude

import DASHI.Biology.DrosophilaSameTrialProvenanceDependenceExact as Fly
import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.SequentialOutcomeBackpropagationBidiExact as Revision

------------------------------------------------------------------------
-- DROSOPHILA SAME-TRIAL EVIDENCE <-> DIAGNOSIS-FIBRE REPAIR
--
-- A mismatch between modalities can remain compatible with observational,
-- registration/frame, model and provenance diagnoses.  Same-trial disagreement
-- is not automatically the biological opposite of a prior interpretation.
------------------------------------------------------------------------

flyDiagnosisFibre : Diagnosis.DiagnosisFibre
flyDiagnosisFibre Outcome.observationConflict = ⊤
flyDiagnosisFibre Outcome.frameConflict = ⊤
flyDiagnosisFibre Outcome.modelConflict = ⊤
flyDiagnosisFibre Outcome.provenanceConflict = ⊤
flyDiagnosisFibre Outcome.insufficientResolution = ⊤
flyDiagnosisFibre _ = ⊥

flyRevision : Outcome.OutcomeDiagnosis → Revision.RevisionAction
flyRevision Outcome.observationConflict = Revision.reacquireObservation
flyRevision Outcome.frameConflict = Revision.rechartRepresentation
flyRevision Outcome.premiseConflict = Revision.inspectPremise
flyRevision Outcome.ruleConflict = Revision.inspectRule
flyRevision Outcome.modelConflict = Revision.reviseModel
flyRevision Outcome.consumerMismatch = Revision.reformulateConsumer
flyRevision Outcome.provenanceConflict = Revision.acquireIndependentProvenance
flyRevision Outcome.authorityMismatch = Revision.seekAuthorityReceipt
flyRevision Outcome.insufficientResolution = Revision.reacquireObservation

registrationOrFrameConflictRequestsRechart :
  flyRevision Outcome.frameConflict ≡ Revision.rechartRepresentation
registrationOrFrameConflictRequestsRechart = refl

sameTrialProvenanceConflictRequestsIndependentReplication :
  flyRevision Outcome.provenanceConflict ≡ Revision.acquireIndependentProvenance
sameTrialProvenanceConflictRequestsIndependentReplication = refl

canonicalDependenceBoundariesRetained :
  List Fly.DependenceBoundary
canonicalDependenceBoundariesRetained = Fly.canonicalDependenceBoundaries

data MultimodalDisagreementMeansBiologicalOpposite : Set where
data SameTrialRepeatCreatesIndependentReplication : Set where

multimodalDisagreementDoesNotMeanBiologicalOpposite :
  MultimodalDisagreementMeansBiologicalOpposite → ⊥
multimodalDisagreementDoesNotMeanBiologicalOpposite ()

sameTrialRepeatDoesNotCreateIndependentReplication :
  SameTrialRepeatCreatesIndependentReplication → ⊥
sameTrialRepeatDoesNotCreateIndependentReplication ()

record DrosophilaDiagnosisSchedulerBoundary : Set where
  constructor drosophila-diagnosis-scheduler-boundary
  field
    modalityMismatchMayHaveMultipleDiagnoses : Bool
    registrationConflictMayRequireRechart : Bool
    provenanceConflictMayRequireIndependentReplication : Bool
    disagreementEqualsBiologicalOpposite : Bool

canonicalDrosophilaDiagnosisSchedulerBoundary : DrosophilaDiagnosisSchedulerBoundary
canonicalDrosophilaDiagnosisSchedulerBoundary =
  drosophila-diagnosis-scheduler-boundary true true true false
