module DASHI.Core.ActiveBidiDiscriminatorLoopExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DiscriminatorSynthesisExact as Disc
import DASHI.Core.SequentialConsumerExperimentPlannerExact as Sequential
import DASHI.Core.SequentialRelationalExperimentPlannerExact as Relational
import DASHI.Core.SequentialRobustActionabilityPlannerExact as Actionability
import DASHI.Core.AdaptiveConsumerModelLoopExact as Adaptive
import DASHI.Core.ReopenableHypothesisForestExact as Forest
import DASHI.Core.GovernedBackwardConsumerRevisionExact as Consumer
import DASHI.Core.AffectedDependencyClosureExact as Dependency
import DASHI.Core.HistoryConditionedChoiceExact as History

------------------------------------------------------------------------
-- ACTIVE BIDI DISCRIMINATOR LOOP
--
-- Domain-neutral orchestration surface for the recurring DASHI cycle:
--
--   live hypotheses
--     -> observer collision
--     -> candidate discriminator / intervention
--     -> backward admission
--     -> measured observation
--     -> live-fibre refinement
--     -> selective dependency reopening
--     -> consumer-closure test
--     -> next experiment or authorised action.
--
-- The forward side may generate candidates.  It does not own truth,
-- intervention authority, refutation, or the definition of success.
------------------------------------------------------------------------

data BidiPhase : Set where
  liveHypotheses
  detectCollision
  generateCandidateDiscriminator
  verifyDiscriminator
  verifyInterventionAuthority
  executeMeasurement
  assimilateEvidence
  refineLiveFibre
  reopenAffectedCertificates
  checkBackwardConsumer
  chooseNextMove
  : BidiPhase

data BidiTransition : BidiPhase → BidiPhase → Set where
  liveToCollision : BidiTransition liveHypotheses detectCollision
  collisionToGenerate : BidiTransition detectCollision generateCandidateDiscriminator
  generateToVerify : BidiTransition generateCandidateDiscriminator verifyDiscriminator
  verifyToAuthority : BidiTransition verifyDiscriminator verifyInterventionAuthority
  authorityToMeasurement : BidiTransition verifyInterventionAuthority executeMeasurement
  measurementToAssimilation : BidiTransition executeMeasurement assimilateEvidence
  assimilationToRefinement : BidiTransition assimilateEvidence refineLiveFibre
  refinementToReopening : BidiTransition refineLiveFibre reopenAffectedCertificates
  reopeningToConsumer : BidiTransition reopenAffectedCertificates checkBackwardConsumer
  consumerToNext : BidiTransition checkBackwardConsumer chooseNextMove
  nextToLive : BidiTransition chooseNextMove liveHypotheses

data BidiPath : BidiPhase → BidiPhase → Set where
  bidiDone : ∀ {phase} → BidiPath phase phase
  bidiStep : ∀ {source middle target} →
    BidiTransition source middle →
    BidiPath middle target →
    BidiPath source target

canonicalOneIterationCycle : BidiPath liveHypotheses liveHypotheses
canonicalOneIterationCycle =
  bidiStep liveToCollision
  (bidiStep collisionToGenerate
  (bidiStep generateToVerify
  (bidiStep verifyToAuthority
  (bidiStep authorityToMeasurement
  (bidiStep measurementToAssimilation
  (bidiStep assimilationToRefinement
  (bidiStep refinementToReopening
  (bidiStep reopeningToConsumer
  (bidiStep consumerToNext
  (bidiStep nextToLive bidiDone))))))))))

data CycleDisposition : Set where
  refineAgain
  actUnderIndependentAuthority
  closeForDeclaredConsumer
  : CycleDisposition

record ActiveBidiCycleReceipt : Set where
  constructor active-bidi-cycle-receipt
  field
    liveHypothesisFibreReference : String
    observerCollisionReference : String
    candidateDiscriminatorReference : String
    nuisanceRobustnessReference : String
    interventionAuthorityReference : String
    measurementCalibrationReference : String
    observationProvenanceReference : String
    evidenceAssimilationReference : String
    refinedFibreReference : String
    affectedDependencyReopeningReference : String
    frozenBackwardConsumerReference : String
    consumerClosureReference : String
    nextFrontierReference : String
    disposition : CycleDisposition

------------------------------------------------------------------------
-- Imported canonical theorem families.
------------------------------------------------------------------------

discriminatorBoundary : Disc.DiscriminatorSynthesisBoundary
discriminatorBoundary = Disc.canonicalDiscriminatorSynthesisBoundary

sequentialBoundary : Sequential.SequentialExperimentPlannerBoundary
sequentialBoundary = Sequential.canonicalSequentialExperimentPlannerBoundary

relationalBoundary : Relational.SequentialRelationalPlannerBoundary
relationalBoundary = Relational.canonicalSequentialRelationalPlannerBoundary

actionabilityBoundary : Actionability.SequentialActionabilityPlannerBoundary
actionabilityBoundary = Actionability.canonicalSequentialActionabilityPlannerBoundary

adaptiveBoundary : Adaptive.AdaptiveConsumerLoopBoundary
adaptiveBoundary = Adaptive.canonicalAdaptiveConsumerLoopBoundary

forestBoundary : Forest.ReopenableHypothesisBoundary
forestBoundary = Forest.canonicalReopenableHypothesisBoundary

consumerBoundary : Consumer.GovernedBackwardConsumerBoundary
consumerBoundary = Consumer.canonicalGovernedBackwardConsumerBoundary

dependencyBoundary : Dependency.DependencyClosureBoundary
dependencyBoundary = Dependency.canonicalDependencyClosureBoundary

historyBoundary : History.HistoryConditionedChoiceBoundary
historyBoundary = History.canonicalHistoryConditionedChoiceBoundary

------------------------------------------------------------------------
-- Exact inherited BIDI boundaries.
------------------------------------------------------------------------

pairwiseSeparationDoesNotCloseWholeConsumer :
  Disc.pairwiseSeparationAutomaticallyClosesWholeConsumerFibre discriminatorBoundary ≡ false
pairwiseSeparationDoesNotCloseWholeConsumer = refl

nextExperimentMayDependOnOutcome :
  Sequential.nextExperimentMayDependOnObservedOutcome sequentialBoundary ≡ true
nextExperimentMayDependOnOutcome = refl

relationalOutcomeMayLeaveAlternativesLive :
  Relational.overlappingOutcomeSupportCanLeaveHypothesesUnresolved relationalBoundary ≡ true
relationalOutcomeMayLeaveAlternativesLive = refl

robustSupportDoesNotCreateAuthority :
  Actionability.robustSupportAutomaticallyCreatesAuthority actionabilityBoundary ≡ false
robustSupportDoesNotCreateAuthority = refl

evidenceUpdateDoesNotReopenEverything :
  Adaptive.evidenceUpdateRequiresEveryCertificateToReopen adaptiveBoundary ≡ false
evidenceUpdateDoesNotReopenEverything = refl

dependencyAffectedCertificatesReopen :
  Adaptive.dependencyAffectedCertificatesMustBeReconsidered adaptiveBoundary ≡ true
dependencyAffectedCertificatesReopen = refl

producerCannotRewriteConsumer :
  Consumer.producerMayRewriteAcceptanceLanguage consumerBoundary ≡ false
producerCannotRewriteConsumer = refl

dormantDoesNotMeanRefuted :
  Forest.inactiveDoesNotMeanRefuted forestBoundary ≡ true
dormantDoesNotMeanRefuted = refl

samePresentNeedNotFixHistorySensitiveChoice :
  History.samePresentObservationImpliesSameChoice historyBoundary ≡ false
samePresentNeedNotFixHistorySensitiveChoice = refl

------------------------------------------------------------------------
-- Cross-domain boundary.
------------------------------------------------------------------------

record ActiveBidiDiscriminatorLoopBoundary : Set where
  constructor active-bidi-discriminator-loop-boundary
  field
    forwardCandidateGenerationChangesWorldTruth : Bool
    forwardCandidateGenerationChangesWorldTruthIsFalse :
      forwardCandidateGenerationChangesWorldTruth ≡ false
    oneDiscriminatorClosesEveryLiveConsumer : Bool
    oneDiscriminatorClosesEveryLiveConsumerIsFalse :
      oneDiscriminatorClosesEveryLiveConsumer ≡ false
    measurementRefutesEveryUnselectedHypothesis : Bool
    measurementRefutesEveryUnselectedHypothesisIsFalse :
      measurementRefutesEveryUnselectedHypothesis ≡ false
    robustInterventionCreatesItsOwnAuthority : Bool
    robustInterventionCreatesItsOwnAuthorityIsFalse :
      robustInterventionCreatesItsOwnAuthority ≡ false
    producerMayWeakenBackwardConsumer : Bool
    producerMayWeakenBackwardConsumerIsFalse :
      producerMayWeakenBackwardConsumer ≡ false
    nextDiscriminatorMayDependOnHistoryAndOutcome : Bool
    nextDiscriminatorMayDependOnHistoryAndOutcomeIsTrue :
      nextDiscriminatorMayDependOnHistoryAndOutcome ≡ true
    evidenceUpdateUsesSelectiveDependencyReopening : Bool
    evidenceUpdateUsesSelectiveDependencyReopeningIsTrue :
      evidenceUpdateUsesSelectiveDependencyReopening ≡ true
    consumerClosureMayPrecedeFullWorldIdentification : Bool
    consumerClosureMayPrecedeFullWorldIdentificationIsTrue :
      consumerClosureMayPrecedeFullWorldIdentification ≡ true
    loopReturnsToLiveHypothesisPhase : Bool
    loopReturnsToLiveHypothesisPhaseIsTrue :
      loopReturnsToLiveHypothesisPhase ≡ true
    reading : String

canonicalActiveBidiDiscriminatorLoopBoundary : ActiveBidiDiscriminatorLoopBoundary
canonicalActiveBidiDiscriminatorLoopBoundary =
  active-bidi-discriminator-loop-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    "BIDI is an active governed cycle: forward search generates hypotheses, discriminators and candidate interventions; backward consumers independently verify discrimination, authority, provenance, nuisance robustness and closure. Observations refine the live fibre, dependency-affected certificates reopen selectively, and the next experiment may depend on realised outcome and history before the cycle returns to the live-hypothesis frontier."
