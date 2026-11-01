module DASHI.Culture.JohnAnthonyBrownDiagnosisRepairSchedulerBidiExact where

open import DASHI.Core.Prelude

import DASHI.Culture.JohnAnthonyBrownReceptionEvidenceReopeningBridgeExact as Brown
import DASHI.Core.DiagnosisFibreSalienceSchedulerBidiExact as Diagnosis
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.SequentialOutcomeBackpropagationBidiExact as Revision

------------------------------------------------------------------------
-- JOHN ANTHONY BROWN PAPER / RECEPTION-AUDIT DIAGNOSIS SCHEDULER
------------------------------------------------------------------------

brownDiagnosisFibre : Diagnosis.DiagnosisFibre
brownDiagnosisFibre Outcome.observationConflict = ⊤
brownDiagnosisFibre Outcome.frameConflict = ⊤
brownDiagnosisFibre Outcome.modelConflict = ⊤
brownDiagnosisFibre Outcome.consumerMismatch = ⊤
brownDiagnosisFibre Outcome.provenanceConflict = ⊤
brownDiagnosisFibre Outcome.authorityMismatch = ⊤
brownDiagnosisFibre Outcome.insufficientResolution = ⊤
brownDiagnosisFibre _ = ⊥

brownRevision : Outcome.OutcomeDiagnosis → Revision.RevisionAction
brownRevision Outcome.observationConflict = Revision.reacquireObservation
brownRevision Outcome.frameConflict = Revision.rechartRepresentation
brownRevision Outcome.premiseConflict = Revision.inspectPremise
brownRevision Outcome.ruleConflict = Revision.inspectRule
brownRevision Outcome.modelConflict = Revision.reviseModel
brownRevision Outcome.consumerMismatch = Revision.reformulateConsumer
brownRevision Outcome.provenanceConflict = Revision.acquireIndependentProvenance
brownRevision Outcome.authorityMismatch = Revision.seekAuthorityReceipt
brownRevision Outcome.insufficientResolution = Revision.reacquireObservation

receptionFrameConflictRequestsRechart :
  brownRevision Outcome.frameConflict ≡ Revision.rechartRepresentation
receptionFrameConflictRequestsRechart = refl

measurementConflictRequestsReacquisition :
  brownRevision Outcome.observationConflict ≡ Revision.reacquireObservation
measurementConflictRequestsReacquisition = refl

confoundingConflictRequestsModelRevision :
  brownRevision Outcome.modelConflict ≡ Revision.reviseModel
confoundingConflictRequestsModelRevision = refl

authorityMismatchRequestsAuthorityReceipt :
  brownRevision Outcome.authorityMismatch ≡ Revision.seekAuthorityReceipt
authorityMismatchRequestsAuthorityReceipt = refl

selectiveReopeningBoundaryRetained : Brown.JohnBrownSelectiveReopeningBoundary
selectiveReopeningBoundaryRetained = Brown.canonicalJohnBrownSelectiveReopeningBoundary

data AdverseAuditResultMeansOppositeHypothesis : Set where
data ReopenedClaimMeansPaperRefuted : Set where
data ExternalReceptionSourceBecomesPaperAuthor : Set where

adverseAuditDoesNotSelectOppositeHypothesis :
  AdverseAuditResultMeansOppositeHypothesis → ⊥
adverseAuditDoesNotSelectOppositeHypothesis ()

reopenedClaimDoesNotMeanPaperRefuted : ReopenedClaimMeansPaperRefuted → ⊥
reopenedClaimDoesNotMeanPaperRefuted ()

externalReceptionSourceDoesNotBecomePaperAuthor :
  ExternalReceptionSourceBecomesPaperAuthor → ⊥
externalReceptionSourceDoesNotBecomePaperAuthor ()

record JohnBrownDiagnosisSchedulerBoundary : Set where
  constructor john-brown-diagnosis-scheduler-boundary
  field
    multipleAuditDiagnosesMayRemainLive : Bool
    frameConflictMayRequestRechart : Bool
    observationConflictMayRequestReacquisition : Bool
    modelConflictMayRequestModelRevision : Bool
    adverseAuditEqualsOppositeHypothesis : Bool
    reopenedClaimEqualsPaperRefutation : Bool

canonicalJohnBrownDiagnosisSchedulerBoundary : JohnBrownDiagnosisSchedulerBoundary
canonicalJohnBrownDiagnosisSchedulerBoundary =
  john-brown-diagnosis-scheduler-boundary true true true true false false
