module DASHI.Biology.AliceBrownTemporalDiagnosisDependencyLineageBidiExact where

open import DASHI.Core.Prelude

import DASHI.Biology.AliceBrownCorpusLoom as Alice
import DASHI.Biology.AliceBrownDissentGovernanceCrossPollinationExact as Dissent
import DASHI.Governance.AliceBrownInstitutionalAgencyChoiceBridgeExact as Agency
import DASHI.Core.AffectedDependencyClosureExact as Closure
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.DiagnosisExperimentPortfolioBidiExact as Portfolio
import DASHI.Core.TemporalDiagnosisProvenanceHistoryBidiExact as Temporal
import DASHI.Core.TemporalDiagnosisDependencyLineageBidiExact as Lineage

------------------------------------------------------------------------
-- ALICE BROWN CORPUS / EPISTEMIC-AGENCY TEMPORAL DIAGNOSIS LINEAGE
--
-- This is a DASHI methodological graph over existing source-bound distinctions.
-- It does not attribute these diagnosis events to the source papers themselves.
------------------------------------------------------------------------

data AliceAuditArtifact : Set where
  surveyFeedbackSurface : AliceAuditArtifact
  studentVoiceSurface : AliceAuditArtifact
  participationAgencyConsumer : AliceAuditArtifact
  parentObserverEvidence : AliceAuditArtifact
  institutionObserverEvidence : AliceAuditArtifact
  multiObserverConsumer : AliceAuditArtifact


data AliceDepends : AliceAuditArtifact → AliceAuditArtifact → Set where
  surveyFeedsVoiceAudit : AliceDepends surveyFeedbackSurface studentVoiceSurface
  voiceFeedsAgencyAudit : AliceDepends studentVoiceSurface participationAgencyConsumer
  parentFeedsMultiObserver : AliceDepends parentObserverEvidence multiObserverConsumer
  institutionFeedsMultiObserver : AliceDepends institutionObserverEvidence multiObserverConsumer

surveyToAgencyPath :
  Closure.AffectedClosure AliceDepends surveyFeedbackSurface participationAgencyConsumer
surveyToAgencyPath =
  Closure.affectedStep surveyFeedsVoiceAudit
    (Closure.affectedStep voiceFeedsAgencyAudit Closure.affectedRefl)

parentToMultiObserverPath :
  Closure.AffectedClosure AliceDepends parentObserverEvidence multiObserverConsumer
parentToMultiObserverPath = Closure.affectedStep parentFeedsMultiObserver Closure.affectedRefl

aliceFrameEliminationEvent : Temporal.DiagnosisEvent Outcome.frameConflict
aliceFrameEliminationEvent =
  Temporal.diagnosis-event
    Temporal.eliminated 1
    (Temporal.debugMoveTrigger Portfolio.frameControl)
    "frame control distinguishes a survey/feedback framing from the current voice/agency audit"
    "Alice Brown methodology x-pollination; not an empirical source-paper event"

aliceFrameReactivationEvent : Temporal.DiagnosisEvent Outcome.frameConflict
aliceFrameReactivationEvent =
  Temporal.diagnosis-event
    Temporal.reactivated 2
    (Temporal.resultTrigger Outcome.indeterminate)
    "later observer evidence makes the framing distinction relevant again"
    "append-only methodological reactivation; source fibres preserved"

aliceFrameEliminationLineage :
  Lineage.DiagnosisLineageEvent AliceDepends Outcome.frameConflict
aliceFrameEliminationLineage =
  Lineage.diagnosis-lineage-event
    aliceFrameEliminationEvent
    surveyFeedbackSurface
    participationAgencyConsumer
    surveyToAgencyPath
    "survey feedback -> student voice audit -> participation/agency consumer"
    "source paper motivates coordinates but does not supply DASHI theorem authority"

aliceFrameReactivationLineage :
  Lineage.DiagnosisLineageEvent AliceDepends Outcome.frameConflict
aliceFrameReactivationLineage =
  Lineage.diagnosis-lineage-event
    aliceFrameReactivationEvent
    parentObserverEvidence
    multiObserverConsumer
    parentToMultiObserverPath
    "later parent-observer evidence -> multi-observer consumer"
    "parent observer remains situated evidence, not replacement for student voice"

aliceCorpusRetained : Alice.AliceBrownCorpusLoom
aliceCorpusRetained = Alice.canonicalAliceBrownCorpusLoom

dissentBoundaryRetained : Dissent.AliceBrownDissentGovernanceBoundary
dissentBoundaryRetained = Dissent.canonicalAliceBrownDissentGovernanceBoundary

institutionalAgencyBoundaryRetained : Agency.AliceInstitutionalChoiceBoundary
institutionalAgencyBoundaryRetained = Agency.canonicalAliceInstitutionalChoiceBoundary

data ParentObserverReplacesStudentVoice : Set where
data ReactivatedFrameDiagnosisProvesInstitutionalWrong : Set where
data AliceSourcePaperAuthoredTemporalDiagnosis : Set where

data SameDiagnosisForcesSameConsumer : Set where

parentObserverDoesNotReplaceStudentVoice : ParentObserverReplacesStudentVoice → ⊥
parentObserverDoesNotReplaceStudentVoice ()

reactivationDoesNotProveInstitutionalWrong :
  ReactivatedFrameDiagnosisProvesInstitutionalWrong → ⊥
reactivationDoesNotProveInstitutionalWrong ()

sourcePaperDoesNotAuthorDashITemporalDiagnosis :
  AliceSourcePaperAuthoredTemporalDiagnosis → ⊥
sourcePaperDoesNotAuthorDashITemporalDiagnosis ()

sameDiagnosisDoesNotForceSameConsumer : SameDiagnosisForcesSameConsumer → ⊥
sameDiagnosisDoesNotForceSameConsumer ()

record AliceBrownTemporalDiagnosisBoundary : Set where
  constructor alice-brown-temporal-diagnosis-boundary
  field
    diagnosisEventCarriesDependencyPath : Bool
    observerFibresRemainDistinct : Bool
    frameDiagnosisMayReactivate : Bool
    sameDiagnosisForcesSameConsumer : Bool
    reactivationTransfersObserverIdentity : Bool
    reactivationProvesInstitutionalWrong : Bool
    sourcePaperAuthorshipTransfersToDashIConstruction : Bool

canonicalAliceBrownTemporalDiagnosisBoundary : AliceBrownTemporalDiagnosisBoundary
canonicalAliceBrownTemporalDiagnosisBoundary =
  alice-brown-temporal-diagnosis-boundary true true true false false false false
