module DASHI.Law.SensibLawParetoProofDirectedCorpusSearchEverything where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawProofDirectedCorpusSearchEverything as Corpus
import DASHI.Law.SensibLawParetoProofDirectedCorpusSearchBidiExact as ParetoSearch
import DASHI.Law.SensibLawAdaptiveLegalResearchFeedbackLoopExact as Feedback
import DASHI.Law.SensibLawConcreteDutyRefinementParetoRerunExact as ConcreteDuty
import DASHI.Law.SensibLawPabaiDefeaterRefinementRerunExact as PabaiRerun
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Intent
import DASHI.Law.SensibLawProofSearchResultAssessmentExact as Assessment
import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawLegalGraphRefinementReopeningExact as Refinement
import DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact as Residual
import DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact as Pareto
import DASHI.Cognition.PNF.SensibLawNegligenceDutyGenericParetoFrontierExact as DutyPareto
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawFiniteLegalSearchRegressionExact as Regression
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence

proofGapStillPrecedesQuery :
  Corpus.ProofDirectedCorpusSearchContract.proofGapPrecedesQueryString
    Corpus.canonicalProofDirectedCorpusSearchContract ≡ true
proofGapStillPrecedesQuery = refl

retrievalStillRequiresAssessment :
  Corpus.ProofDirectedCorpusSearchContract.retrievalRequiresProofAssessment
    Corpus.canonicalProofDirectedCorpusSearchContract ≡ true
retrievalStillRequiresAssessment = refl

corePolicyDirectiveUsesAuthorityTreatment :
  ParetoSearch.CertifiedSearchDirective.producerClass ParetoSearch.corePolicySearchDirective
  ≡ Intent.authorityTreatmentProducer
corePolicyDirectiveUsesAuthorityTreatment = refl

statutoryDirectiveUsesExactAuthority :
  ParetoSearch.CertifiedSearchDirective.producerClass ParetoSearch.statutoryCoherenceSearchDirective
  ≡ Intent.exactCitedAuthorityProducer
statutoryDirectiveUsesExactAuthority = refl

herzogIncidentDirectiveUsesOccurrenceEvidence :
  ParetoSearch.CertifiedSearchDirective.producerClass ParetoSearch.herzogIncidentWeldSearchDirective
  ≡ Intent.occurrenceEvidenceProducer
herzogIncidentDirectiveUsesOccurrenceEvidence = refl

admittedClosedResultMayBecomeStopCandidate :
  Feedback.feedbackDisposition Assessment.proofPaymentAdmitted Assessment.frontierClosed
  ≡ Feedback.stopCandidate
admittedClosedResultMayBecomeStopCandidate = refl

admittedNarrowingRecomputesFrontier :
  Feedback.feedbackDisposition Assessment.proofPaymentAdmitted Assessment.frontierNarrowed
  ≡ Feedback.recomputeFrontier
admittedNarrowingRecomputesFrontier = refl

contradictoryResultReopensForDefeater :
  Feedback.feedbackDisposition Assessment.proofPaymentRejected Assessment.frontierContradicted
  ≡ Feedback.reopenForDefeater
contradictoryResultReopensForDefeater = refl

statutoryCoherenceFeedbackReturnsToStatute :
  Refinement.LegalSelectiveReopenRequest.acquisition Feedback.statutoryCoherenceReopenRequest
  ≡ Residual.inspectStatutoryText
statutoryCoherenceFeedbackReturnsToStatute = refl

------------------------------------------------------------------------
-- Concrete scheduler-state rerun for duty.
------------------------------------------------------------------------

concreteDutyRefinementPreservesHistory :
  Refinement.LegalRefinementReceipt.oldHistoryPreserved ConcreteDuty.policyAssessmentRefinementReceipt
  ≡ true
concreteDutyRefinementPreservesHistory = refl

concreteDutyRefinementForcesRecompute :
  Refinement.LegalRefinementReceipt.conclusionsMustBeRecomputed ConcreteDuty.policyAssessmentRefinementReceipt
  ≡ true
concreteDutyRefinementForcesRecompute = refl

concreteDutyOldFrontierIsCorePolicy :
  Pareto.paretoFrontier DutyPareto.currentDutyPortfolio
  ≡ DutyPareto.currentCorePolicyCell ∷ []
concreteDutyOldFrontierIsCorePolicy = ConcreteDuty.frontierBeforePolicyAssessment

concreteDutyNewFrontierIsStatutoryCoherence :
  Pareto.paretoFrontier DutyPareto.postPolicyPortfolio
  ≡ DutyPareto.postPolicyStatutoryCoherenceCell ∷ []
concreteDutyNewFrontierIsStatutoryCoherence = ConcreteDuty.frontierAfterPolicyAssessment

concreteDutySelectedCoordinateActuallyChanges :
  Pareto.requirement DutyPareto.currentCorePolicyCell
  ≡ Pareto.requirement DutyPareto.postPolicyStatutoryCoherenceCell
  → ⊥
concreteDutySelectedCoordinateActuallyChanges = ConcreteDuty.selectedRequirementChanges

------------------------------------------------------------------------
-- Concrete non-monotone legal rerun on the existing non-empty Pabai graph.
------------------------------------------------------------------------

pabaiAppendOnlyDefeaterRefinementPreservesHistory :
  Refinement.LegalRefinementReceipt.oldHistoryPreserved PabaiRerun.pabaiDefeaterRefinementReceipt
  ≡ true
pabaiAppendOnlyDefeaterRefinementPreservesHistory = refl

pabaiWasReachableBeforeDefeater :
  Search.reachable 1 Regression.pabaiGraph PabaiRerun.pabaiFactsBeforeDefeater
    Negligence.dutyProposition ≡ true
pabaiWasReachableBeforeDefeater = PabaiRerun.pabaiReachableBeforeDefeater

pabaiHasProofRelevantDutyBeforeDefeater :
  Algebra.Reachable Regression.pabaiGraph PabaiRerun.pabaiFactsBeforeDefeater
    Negligence.dutyProposition
pabaiHasProofRelevantDutyBeforeDefeater = PabaiRerun.pabaiDutyProofBeforeDefeater

pabaiBecomesUnreachableAfterDefeater :
  Search.reachable 1 Regression.pabaiGraph PabaiRerun.pabaiFactsAfterDefeater
    Negligence.dutyProposition ≡ false
pabaiBecomesUnreachableAfterDefeater = PabaiRerun.pabaiUnreachableAfterDefeater

pabaiHasNoProofRelevantDutyAfterDefeater :
  Algebra.Reachable Regression.pabaiGraph PabaiRerun.pabaiFactsAfterDefeater
    Negligence.dutyProposition → ⊥
pabaiHasNoProofRelevantDutyAfterDefeater = PabaiRerun.pabaiDutyImpossibleAfterDefeater

pabaiRepairSearchStillReopensCandidate :
  Search.firstReopeningTransformation 1 Negligence.dutyProposition
    (Regression.pabaiReformulationCandidate ∷ [])
  ≡ Search.found Regression.pabaiReformulationCandidate
pabaiRepairSearchStillReopensCandidate = PabaiRerun.pabaiExistingRepairCandidateStillReopens

paretoCertificateStillDoesNotPayGap :
  ParetoSearch.ParetoCertificateAutomaticallyPaysProofGap → ⊥
paretoCertificateStillDoesNotPayGap = ParetoSearch.aParetoCertificateOnlySchedules

retrievedSourceStillDoesNotAutoPayRequirement :
  ParetoSearch.RetrievedDocumentAutomaticallyPaysRequirement → ⊥
retrievedSourceStillDoesNotAutoPayRequirement = ParetoSearch.retrievalStillNeedsAssessment

data SearchDirectiveIsLegalAuthority : Set where
data FrontierCertificateMakesRetrievedSourceTrue : Set where
data FeedbackClosureAutomaticallyAuthorisesAction : Set where

directiveIsNotAuthority : SearchDirectiveIsLegalAuthority → ⊥
directiveIsNotAuthority ()

frontierCertificateDoesNotPrejudgeRetrieval : FrontierCertificateMakesRetrievedSourceTrue → ⊥
frontierCertificateDoesNotPrejudgeRetrieval ()

feedbackClosureStillNeedsActionAuthority : FeedbackClosureAutomaticallyAuthorisesAction → ⊥
feedbackClosureStillNeedsActionAuthority ()
