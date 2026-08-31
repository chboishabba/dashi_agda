module DASHI.Reasoning.Spacy369ConsumerRevisionTemporalBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.SpacyNegatedCoordinationScopeTraceExact as Trace
import DASHI.Reasoning.Spacy369AdaptiveConsumerProbeSchedulerExact as Scheduler
import DASHI.Reasoning.Spacy369FeministLacanConsumerRelativeExact as Consumer
import DASHI.Reasoning.Spacy369MultiConsumerSharedProbeExact as Shared
import DASHI.Reasoning.Spacy369MultiConsumerCoverageFiltrationExact as Filtration
import DASHI.Reasoning.Spacy369MultiConsumerCoverageSelectiveReopeningExact as Reopen

------------------------------------------------------------------------
-- TEMPORAL BIDI OVER THE TWO-DIRECTION ARCHITECTURE ITSELF.
--
-- Forward evidence / semantic-PNF / logical-result state is frozen across this
-- finite consumer-revision history.  Backward demand evolves, and therefore the
-- information policy evolves.  A later consumer does not rewrite the earlier
-- answer; it creates a new obligation relative to the enlarged demand surface.
------------------------------------------------------------------------

data RevisionEpoch : Set where
  operationalEpoch subjectStandingEpoch allConsumersEpoch : RevisionEpoch

consumerAt : RevisionEpoch → Scheduler.ConsumerBundle
consumerAt operationalEpoch = Scheduler.operationalOnly
consumerAt subjectStandingEpoch = Scheduler.subjectAndStanding
consumerAt allConsumersEpoch = Scheduler.subjectStandingAndClosure

scheduleAt : RevisionEpoch → Scheduler.ScheduledPlan
scheduleAt epoch = Scheduler.schedule (consumerAt epoch)

operationalSchedule : scheduleAt operationalEpoch ≡ Scheduler.stopNow
operationalSchedule = refl

subjectStandingSchedule :
  scheduleAt subjectStandingEpoch ≡ Scheduler.runSharedContext
subjectStandingSchedule = refl

allConsumerSchedule :
  scheduleAt allConsumersEpoch ≡ Scheduler.runSharedThenClosure
allConsumerSchedule = refl

------------------------------------------------------------------------
-- Frozen forward spine.
------------------------------------------------------------------------

record ForwardSpine : Set₁ where
  constructor forwardSpine
  field
    parserCandidate : Candidate.CandidateSemanticFragment
    parserCandidateExact : parserCandidate ≡ Trace.negNarrowCandidate
    parserReviewExact : Trace.revised369 ≡ Trace.revised369
    finalFormulaExact : Trace.finalFormula ≡ Trace.finalFormula

open ForwardSpine public

forwardAt : RevisionEpoch → ForwardSpine
forwardAt epoch = forwardSpine Trace.negNarrowCandidate refl refl refl

forwardSpineFrozen01 : forwardAt operationalEpoch ≡ forwardAt subjectStandingEpoch
forwardSpineFrozen01 = refl

forwardSpineFrozen12 : forwardAt subjectStandingEpoch ≡ forwardAt allConsumersEpoch
forwardSpineFrozen12 = refl

------------------------------------------------------------------------
-- Backward demand spine.
------------------------------------------------------------------------

record BackwardSpine : Set where
  constructor backwardSpine
  field
    declaredConsumer : Scheduler.ConsumerBundle
    selectedSchedule : Scheduler.ScheduledPlan
    scheduleExact : selectedSchedule ≡ Scheduler.schedule declaredConsumer

open BackwardSpine public

backwardAt : RevisionEpoch → BackwardSpine
backwardAt epoch = backwardSpine (consumerAt epoch) (scheduleAt epoch) refl

backwardChanges01 :
  selectedSchedule (backwardAt operationalEpoch)
  ≡ selectedSchedule (backwardAt subjectStandingEpoch) → ⊥
backwardChanges01 ()

backwardChanges12 :
  selectedSchedule (backwardAt subjectStandingEpoch)
  ≡ selectedSchedule (backwardAt allConsumersEpoch) → ⊥
backwardChanges12 ()

------------------------------------------------------------------------
-- Proof-relevant consumer revision edges.
------------------------------------------------------------------------

data ConsumerRevision : RevisionEpoch → RevisionEpoch → Set where
  addSubjectStanding : ConsumerRevision operationalEpoch subjectStandingEpoch
  addClosureResidual : ConsumerRevision subjectStandingEpoch allConsumersEpoch

record ConsumerRevisionReceipt
    {before after : RevisionEpoch}
    (revision : ConsumerRevision before after) : Set₁ where
  constructor consumerRevisionReceipt
  field
    forwardFrozen : forwardAt before ≡ forwardAt after
    scheduleChanged : scheduleAt before ≡ scheduleAt after → ⊥
    revisionAddsDemandReference : String
    previousSufficiencyRetainedReference : String

open ConsumerRevisionReceipt public

operationalToSubjectStanding : ConsumerRevisionReceipt addSubjectStanding
operationalToSubjectStanding =
  consumerRevisionReceipt
    refl
    (λ ())
    "new backward demand: subject position + governed standing"
    "operational closure remains historically valid for its original consumer"

subjectStandingToAll : ConsumerRevisionReceipt addClosureResidual
subjectStandingToAll =
  consumerRevisionReceipt
    refl
    (λ ())
    "new backward demand: closure/excluded residual"
    "shared-context closure remains historically valid for subject/standing consumers"

------------------------------------------------------------------------
-- Historical sufficiency is indexed by the consumer that was actually asked.
------------------------------------------------------------------------

data HistoricallySufficient : RevisionEpoch → Set₁ where
  operationalWasSufficient :
    Consumer.operationalClosureReceipt ≡ Consumer.operationalClosureReceipt →
    HistoricallySufficient operationalEpoch
  subjectStandingWasSufficient :
    Shared.sharedProbeClosesSubjectConsumer
      ≡ Shared.sharedProbeClosesSubjectConsumer →
    Shared.sharedProbeClosesStandingConsumer
      ≡ Shared.sharedProbeClosesStandingConsumer →
    HistoricallySufficient subjectStandingEpoch
  allConsumersWereCovered :
    Filtration.FirstClosureAt
      Filtration.closureResidualConsumer Filtration.depth2 →
    HistoricallySufficient allConsumersEpoch

operationalHistoricalSufficiency : HistoricallySufficient operationalEpoch
operationalHistoricalSufficiency = operationalWasSufficient refl

subjectStandingHistoricalSufficiency : HistoricallySufficient subjectStandingEpoch
subjectStandingHistoricalSufficiency = subjectStandingWasSufficient refl refl

allConsumerHistoricalSufficiency : HistoricallySufficient allConsumersEpoch
allConsumerHistoricalSufficiency =
  allConsumersWereCovered Filtration.closureResidualFirstAt2

------------------------------------------------------------------------
-- Global completeness is intentionally stronger than historical sufficiency.
------------------------------------------------------------------------

data GloballyCompleteAt : RevisionEpoch → Set where
  globallyCompleteAtAllConsumers : GloballyCompleteAt allConsumersEpoch

operationalWasSufficientButNotGloballyComplete :
  HistoricallySufficient operationalEpoch × (GloballyCompleteAt operationalEpoch → ⊥)
operationalWasSufficientButNotGloballyComplete =
  operationalHistoricalSufficiency , (λ ())

subjectStandingWasSufficientButNotGloballyComplete :
  HistoricallySufficient subjectStandingEpoch ×
  (GloballyCompleteAt subjectStandingEpoch → ⊥)
subjectStandingWasSufficientButNotGloballyComplete =
  subjectStandingHistoricalSufficiency , (λ ())

------------------------------------------------------------------------
-- New consumer demand creates a NEW obligation rather than falsifying the old
-- indexed closure receipt.
------------------------------------------------------------------------

data NewDemandObligation :
    ∀ {before after} → ConsumerRevision before after → Set where
  acquireSharedContext : NewDemandObligation addSubjectStanding
  acquireClosureResidual : NewDemandObligation addClosureResidual

obligationFor :
  ∀ {before after} →
  (revision : ConsumerRevision before after) →
  NewDemandObligation revision
obligationFor addSubjectStanding = acquireSharedContext
obligationFor addClosureResidual = acquireClosureResidual

oldOperationalReceiptSurvivesRevision :
  ConsumerRevision operationalEpoch subjectStandingEpoch →
  HistoricallySufficient operationalEpoch
oldOperationalReceiptSurvivesRevision addSubjectStanding =
  operationalHistoricalSufficiency

oldSubjectStandingReceiptSurvivesRevision :
  ConsumerRevision subjectStandingEpoch allConsumersEpoch →
  HistoricallySufficient subjectStandingEpoch
oldSubjectStandingReceiptSurvivesRevision addClosureResidual =
  subjectStandingHistoricalSufficiency

------------------------------------------------------------------------
-- Reopening is consumer/demand relative, not retroactive refutation.
------------------------------------------------------------------------

sharedContextReopeningAnchor = Reopen.sharedContextReopensSubject
closureResidualReopeningAnchor = Reopen.closureResidualReopensClosureOnly

------------------------------------------------------------------------
-- BIDI nonfactorability at the architecture level.
--
-- The identical forward spine cannot determine the backward scheduler because
-- different consumer epochs keep the forward object fixed while selecting
-- different schedules.
------------------------------------------------------------------------

forwardObserver : RevisionEpoch → ForwardSpine
forwardObserver = forwardAt

backwardPolicyObserver : RevisionEpoch → Scheduler.ScheduledPlan
backwardPolicyObserver = scheduleAt

forwardSameOperationalAll :
  forwardObserver operationalEpoch ≡ forwardObserver allConsumersEpoch
forwardSameOperationalAll = refl

backwardPolicyDiffersOperationalAll :
  backwardPolicyObserver operationalEpoch
  ≡ backwardPolicyObserver allConsumersEpoch → ⊥
backwardPolicyDiffersOperationalAll ()

forwardSpineCannotRecoverBackwardPolicy :
  INF.FactorsThrough forwardObserver backwardPolicyObserver → ⊥
forwardSpineCannotRecoverBackwardPolicy =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      operationalEpoch
      allConsumersEpoch
      forwardSameOperationalAll
      backwardPolicyDiffersOperationalAll)

------------------------------------------------------------------------
-- Conversely, the evolving backward policy is not authority to rewrite the
-- frozen forward evidence.  This is captured positively by the revision
-- receipts' forwardFrozen fields and negatively in the boundary below.
------------------------------------------------------------------------

record Spacy369ConsumerRevisionTemporalBidiBoundary : Set where
  constructor spacy369ConsumerRevisionTemporalBidiBoundary
  field
    consumerRevisionMayChangeSchedule : Bool
    consumerRevisionMayChangeScheduleIsTrue :
      consumerRevisionMayChangeSchedule ≡ true
    consumerRevisionRewritesMaterialisedParserEvidence : Bool
    consumerRevisionRewritesMaterialisedParserEvidenceIsFalse :
      consumerRevisionRewritesMaterialisedParserEvidence ≡ false
    consumerRevisionRewritesReviewedFormula : Bool
    consumerRevisionRewritesReviewedFormulaIsFalse :
      consumerRevisionRewritesReviewedFormula ≡ false
    newConsumerDemandCreatesNewObligation : Bool
    newConsumerDemandCreatesNewObligationIsTrue :
      newConsumerDemandCreatesNewObligation ≡ true
    newConsumerDemandMakesOldIndexedAnswerFalse : Bool
    newConsumerDemandMakesOldIndexedAnswerFalseIsFalse :
      newConsumerDemandMakesOldIndexedAnswerFalse ≡ false
    oldConsumerSufficiencyMeansGlobalCompleteness : Bool
    oldConsumerSufficiencyMeansGlobalCompletenessIsFalse :
      oldConsumerSufficiencyMeansGlobalCompleteness ≡ false
    forwardSpineAloneDeterminesBackwardPolicy : Bool
    forwardSpineAloneDeterminesBackwardPolicyIsFalse :
      forwardSpineAloneDeterminesBackwardPolicy ≡ false

canonicalSpacy369ConsumerRevisionTemporalBidiBoundary :
  Spacy369ConsumerRevisionTemporalBidiBoundary
canonicalSpacy369ConsumerRevisionTemporalBidiBoundary =
  spacy369ConsumerRevisionTemporalBidiBoundary
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl
    false refl
