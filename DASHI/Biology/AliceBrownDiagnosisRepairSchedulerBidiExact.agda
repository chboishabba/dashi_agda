module DASHI.Biology.AliceBrownDiagnosisRepairSchedulerBidiExact where

open import DASHI.Core.Prelude

import DASHI.Biology.AliceBrownDissentGovernanceCrossPollinationExact as Dissent
import DASHI.Governance.AliceBrownInstitutionalAgencyChoiceBridgeExact as Agency
import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.SequentialOutcomeBackpropagationBidiExact as Revision

------------------------------------------------------------------------
-- ALICE BROWN EPISTEMIC-AGENCY / OBSERVER-PLURALITY DIAGNOSIS SCHEDULER
------------------------------------------------------------------------

aliceDiagnosisFibre : Diagnosis.DiagnosisFibre
aliceDiagnosisFibre Outcome.observationConflict = ⊤
aliceDiagnosisFibre Outcome.frameConflict = ⊤
aliceDiagnosisFibre Outcome.consumerMismatch = ⊤
aliceDiagnosisFibre Outcome.provenanceConflict = ⊤
aliceDiagnosisFibre Outcome.authorityMismatch = ⊤
aliceDiagnosisFibre Outcome.insufficientResolution = ⊤
aliceDiagnosisFibre _ = ⊥

aliceRevision : Outcome.OutcomeDiagnosis → Revision.RevisionAction
aliceRevision Outcome.observationConflict = Revision.reacquireObservation
aliceRevision Outcome.frameConflict = Revision.rechartRepresentation
aliceRevision Outcome.premiseConflict = Revision.inspectPremise
aliceRevision Outcome.ruleConflict = Revision.inspectRule
aliceRevision Outcome.modelConflict = Revision.reviseModel
aliceRevision Outcome.consumerMismatch = Revision.reformulateConsumer
aliceRevision Outcome.provenanceConflict = Revision.acquireIndependentProvenance
aliceRevision Outcome.authorityMismatch = Revision.seekAuthorityReceipt
aliceRevision Outcome.insufficientResolution = Revision.reacquireObservation

frameConflictRequestsRechart :
  aliceRevision Outcome.frameConflict ≡ Revision.rechartRepresentation
frameConflictRequestsRechart = refl

consumerMismatchRequestsReformulation :
  aliceRevision Outcome.consumerMismatch ≡ Revision.reformulateConsumer
consumerMismatchRequestsReformulation = refl

authorityMismatchRequestsAuthorityReceipt :
  aliceRevision Outcome.authorityMismatch ≡ Revision.seekAuthorityReceipt
authorityMismatchRequestsAuthorityReceipt = refl

dissentBoundaryRetained : Dissent.AliceBrownDissentGovernanceBoundary
dissentBoundaryRetained = Dissent.canonicalAliceBrownDissentGovernanceBoundary

agencyBoundaryRetained : Agency.AliceInstitutionalChoiceBoundary
agencyBoundaryRetained = Agency.canonicalAliceInstitutionalChoiceBoundary

data FeedbackMismatchMeansStudentVoiceFalse : Set where
data ParentObserverConflictTransfersStudentIdentity : Set where
data AuthorityMismatchSolvedByMoreObservation : Set where

feedbackMismatchDoesNotMeanStudentVoiceFalse : FeedbackMismatchMeansStudentVoiceFalse → ⊥
feedbackMismatchDoesNotMeanStudentVoiceFalse ()

parentObserverConflictDoesNotTransferStudentIdentity :
  ParentObserverConflictTransfersStudentIdentity → ⊥
parentObserverConflictDoesNotTransferStudentIdentity ()

authorityMismatchNotSolvedByObservationAlone :
  AuthorityMismatchSolvedByMoreObservation → ⊥
authorityMismatchNotSolvedByObservationAlone ()

record AliceBrownDiagnosisSchedulerBoundary : Set where
  constructor alice-brown-diagnosis-scheduler-boundary
  field
    multipleDiagnosesMayRemainLive : Bool
    frameConflictMayCallForRechart : Bool
    consumerMismatchMayCallForReformulation : Bool
    authorityMismatchRequiresSeparateReceipt : Bool
    observerConflictTransfersSubjectIdentity : Bool

canonicalAliceBrownDiagnosisSchedulerBoundary : AliceBrownDiagnosisSchedulerBoundary
canonicalAliceBrownDiagnosisSchedulerBoundary =
  alice-brown-diagnosis-scheduler-boundary true true true true false
