module DASHI.Biology.AliceBrownSelectiveInvalidationParetoBidiExact where

open import DASHI.Core.Prelude

import DASHI.Biology.AliceBrownDiagnosisRepairSchedulerBidiExact as Diagnosis
import DASHI.Biology.AliceBrownTemporalDiagnosisDependencyLineageBidiExact as Lineage
import DASHI.Core.AffectedDependencyClosureExact as Closure
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.SequentialOutcomeBackpropagationBidiExact as Revision
import DASHI.Core.SelectiveInvalidationParetoFrontierBidiExact as Pareto

------------------------------------------------------------------------
-- ALICE BROWN SELECTIVE INVALIDATION / PARETO RETURN
------------------------------------------------------------------------

voiceAgencyCertificate : Pareto.CertificateCandidate
voiceAgencyCertificate =
  Pareto.certificate-candidate
    "survey -> voice -> participation/agency certificate"
    Outcome.frameConflict
    Pareto.mustRecompute
    0 0 0 2
    "current changed path terminates at participation/agency consumer"

parentObserverCertificate : Pareto.CertificateCandidate
parentObserverCertificate =
  Pareto.certificate-candidate
    "parent observer -> multi-observer certificate"
    Outcome.provenanceConflict
    Pareto.provablyUnaffected
    4 4 0 0
    "different consumer/path; retained unless an explicit path change reaches it"

consumerReformulationCandidate : Pareto.CertificateCandidate
consumerReformulationCandidate =
  Pareto.certificate-candidate
    "participation consumer reformulation"
    Outcome.consumerMismatch
    Pareto.mayRecompute
    2 1 0 1
    "reformulate only if recomputed voice/agency surface changes consumer adequacy"

authorityCertificate : Pareto.CertificateCandidate
authorityCertificate =
  Pareto.certificate-candidate
    "institutional/subject authority receipt"
    Outcome.authorityMismatch
    Pareto.authorityBlocked
    0 0 9 1
    "epistemic repair cannot manufacture subject or institutional authority"

aliceFrameRepairStillRecharts :
  Diagnosis.aliceRevision Outcome.frameConflict ≡ Revision.rechartRepresentation
aliceFrameRepairStillRecharts = Diagnosis.frameConflictRequestsRechart

aliceAuthorityStillSeparate :
  Diagnosis.aliceRevision Outcome.authorityMismatch ≡ Revision.seekAuthorityReceipt
aliceAuthorityStillSeparate = Diagnosis.authorityMismatchRequestsAuthorityReceipt

surveyPathRetained :
  Closure.AffectedClosure
    Lineage.AliceDepends
    Lineage.surveyFeedbackSurface
    Lineage.participationAgencyConsumer
surveyPathRetained = Lineage.surveyToAgencyPath

parentPathRetained :
  Closure.AffectedClosure
    Lineage.AliceDepends
    Lineage.parentObserverEvidence
    Lineage.multiObserverConsumer
parentPathRetained = Lineage.parentToMultiObserverPath

data SurveyChangeReopensParentObserverAutomatically : Set where
data ParetoPreferredVoiceRepairCreatesStudentAuthority : Set where
data SameDiagnosisCollapsesAliceConsumers : Set where

surveyChangeDoesNotReopenParentObserverAutomatically :
  SurveyChangeReopensParentObserverAutomatically → ⊥
surveyChangeDoesNotReopenParentObserverAutomatically ()

paretoPreferenceDoesNotCreateStudentAuthority :
  ParetoPreferredVoiceRepairCreatesStudentAuthority → ⊥
paretoPreferenceDoesNotCreateStudentAuthority ()

sameDiagnosisDoesNotCollapseAliceConsumers : SameDiagnosisCollapsesAliceConsumers → ⊥
sameDiagnosisDoesNotCollapseAliceConsumers ()

record AliceBrownSelectiveInvalidationParetoBoundary : Set where
  constructor alice-brown-selective-invalidation-pareto-boundary
  field
    changedVoicePathMayBeMustRecompute : Bool
    parentObserverPathMayRemainUnaffected : Bool
    consumerReformulationMayRemainConditional : Bool
    authorityPathRemainsBlockedWithoutReceipt : Bool
    paretoRankingTransfersSubjectIdentityOrAuthority : Bool
    ambientParetoCapacityForcesFullAliceCorpusMaterialisation : Bool

canonicalAliceBrownSelectiveInvalidationParetoBoundary :
  AliceBrownSelectiveInvalidationParetoBoundary
canonicalAliceBrownSelectiveInvalidationParetoBoundary =
  alice-brown-selective-invalidation-pareto-boundary
    true true true true false false
