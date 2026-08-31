module DASHI.Reasoning.Spacy369AdaptiveConsumerProbeSchedulerExact where

open import DASHI.Core.Prelude

import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Actionability
import DASHI.Core.AdaptiveConsumerModelLoopExact as Adaptive
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.SpacyNegatedCoordinationScopeTraceExact as Trace
import DASHI.Reasoning.Spacy369MultiConsumerCoverageFiltrationExact as Filtration
import DASHI.Reasoning.Spacy369MultiConsumerCoveragePathResidueExact as Path

------------------------------------------------------------------------
-- ADAPTIVE CONSUMER-INDEXED PROBE SCHEDULER OVER THE MATERIALISED SPACY / 369
-- FIXTURE.
--
-- Changing the declared downstream consumer bundle changes the information
-- policy, not the already-materialised spaCy observation, parser-review chart,
-- or reviewed logical consequence.  Search/resource cost is retained only as
-- the generic actionability calculus defines it; it is not truth or authority.
------------------------------------------------------------------------

data ConsumerBundle : Set where
  operationalOnly
  subjectOnly
  standingOnly
  subjectAndStanding
  closureOnly
  subjectStandingAndClosure
  : ConsumerBundle

data ScheduledPlan : Set where
  stopNow
  runSharedContext
  runClosureResidual
  runSharedThenClosure
  : ScheduledPlan

schedule : ConsumerBundle → ScheduledPlan
schedule operationalOnly = stopNow
schedule subjectOnly = runSharedContext
schedule standingOnly = runSharedContext
schedule subjectAndStanding = runSharedContext
schedule closureOnly = runClosureResidual
schedule subjectStandingAndClosure = runSharedThenClosure

------------------------------------------------------------------------
-- Exact consumer-relative plan changes.
------------------------------------------------------------------------

operationalStops : schedule operationalOnly ≡ stopNow
operationalStops = refl

subjectUsesSharedProbe : schedule subjectOnly ≡ runSharedContext
subjectUsesSharedProbe = refl

standingUsesSameSharedProbe : schedule standingOnly ≡ runSharedContext
standingUsesSameSharedProbe = refl

sharedPairUsesOneProbe : schedule subjectAndStanding ≡ runSharedContext
sharedPairUsesOneProbe = refl

closureUsesIndependentProbe : schedule closureOnly ≡ runClosureResidual
closureUsesIndependentProbe = refl

fullBundleUsesTwoStagePath :
  schedule subjectStandingAndClosure ≡ runSharedThenClosure
fullBundleUsesTwoStagePath = refl

addingClosureConsumerChangesSharedPlan :
  schedule subjectAndStanding ≡ schedule subjectStandingAndClosure → ⊥
addingClosureConsumerChangesSharedPlan ()

addingSubjectStandingChangesClosureOnlyPlan :
  schedule closureOnly ≡ schedule subjectStandingAndClosure → ⊥
addingSubjectStandingChangesClosureOnlyPlan ()

------------------------------------------------------------------------
-- Consumer closure depth predicts the required scheduler shape.
------------------------------------------------------------------------

operationalDepthWitness :
  Filtration.FirstClosureAt
    Filtration.operationalConsumer Filtration.depth0
operationalDepthWitness = Filtration.operationalFirstAt0

subjectDepthWitness :
  Filtration.FirstClosureAt
    Filtration.subjectPositionConsumer Filtration.depth1
subjectDepthWitness = Filtration.subjectFirstAt1

standingDepthWitness :
  Filtration.FirstClosureAt
    Filtration.governedStandingConsumer Filtration.depth1
standingDepthWitness = Filtration.standingFirstAt1

closureDepthWitness :
  Filtration.FirstClosureAt
    Filtration.closureResidualConsumer Filtration.depth2
closureDepthWitness = Filtration.closureResidualFirstAt2

------------------------------------------------------------------------
-- Declared search/resource cost for the selected plan.
------------------------------------------------------------------------

planCost : ScheduledPlan → Nat
planCost stopNow = 0
planCost runSharedContext = Actionability.cost (Path.probeMove Path.sharedContextProbe)
planCost runClosureResidual = Actionability.cost (Path.probeMove Path.closureResidualProbe)
planCost runSharedThenClosure =
  Actionability.cost (Path.probeMove Path.sharedContextProbe)
  + Actionability.cost (Path.probeMove Path.closureResidualProbe)

operationalPlanCost : planCost (schedule operationalOnly) ≡ 0
operationalPlanCost = refl

sharedPlanCost : planCost (schedule subjectAndStanding) ≡ 2
sharedPlanCost = refl

closurePlanCost : planCost (schedule closureOnly) ≡ 1
closurePlanCost = refl

fullPlanCost : planCost (schedule subjectStandingAndClosure) ≡ 3
fullPlanCost = refl

------------------------------------------------------------------------
-- The adaptive-consumer owner is consumed only as a boundary: evidence updates
-- do not require every certificate to reopen.  This local scheduler likewise
-- changes information acquisition according to the declared consumers rather
-- than globally invalidating existing results.
------------------------------------------------------------------------

adaptiveLoopBoundary : Adaptive.AdaptiveConsumerLoopBoundary
adaptiveLoopBoundary = Adaptive.canonicalAdaptiveConsumerLoopBoundary

------------------------------------------------------------------------
-- Scheduler changes do NOT rewrite the forward materialised objects.
------------------------------------------------------------------------

materialisedParserObservation : ConsumerBundle → Candidate.CandidateSemanticFragment
materialisedParserObservation bundle = Trace.negNarrowCandidate

materialisedFinalFormula bundle = Trace.finalFormula

parserObservationInvariantUnderConsumerChange :
  materialisedParserObservation operationalOnly
  ≡ materialisedParserObservation subjectStandingAndClosure
parserObservationInvariantUnderConsumerChange = refl

finalFormulaInvariantUnderConsumerChange :
  materialisedFinalFormula operationalOnly
  ≡ materialisedFinalFormula subjectStandingAndClosure
finalFormulaInvariantUnderConsumerChange = refl

parserReviewAtomInvariantUnderConsumerChange :
  Trace.revised369 ≡ Trace.revised369
parserReviewAtomInvariantUnderConsumerChange = refl

------------------------------------------------------------------------
-- Do not overinterpret cost or scheduling.
------------------------------------------------------------------------

record Spacy369AdaptiveConsumerProbeSchedulerBoundary : Set where
  constructor spacy369AdaptiveConsumerProbeSchedulerBoundary
  field
    changingDeclaredConsumersMayChangeProbePath : Bool
    changingDeclaredConsumersMayChangeProbePathIsTrue :
      changingDeclaredConsumersMayChangeProbePath ≡ true
    operationalConsumerMustPayForCriticalAuditProbes : Bool
    operationalConsumerMustPayForCriticalAuditProbesIsFalse :
      operationalConsumerMustPayForCriticalAuditProbes ≡ false
    oneSharedProbeMayServeSeveralConsumers : Bool
    oneSharedProbeMayServeSeveralConsumersIsTrue :
      oneSharedProbeMayServeSeveralConsumers ≡ true
    addingConsumerRewritesMaterialisedParserEvidence : Bool
    addingConsumerRewritesMaterialisedParserEvidenceIsFalse :
      addingConsumerRewritesMaterialisedParserEvidence ≡ false
    addingConsumerRewritesReviewedLogicalFormula : Bool
    addingConsumerRewritesReviewedLogicalFormulaIsFalse :
      addingConsumerRewritesReviewedLogicalFormula ≡ false
    schedulerCostIsTruthValue : Bool
    schedulerCostIsTruthValueIsFalse : schedulerCostIsTruthValue ≡ false
    schedulerCostIsEpistemicAuthority : Bool
    schedulerCostIsEpistemicAuthorityIsFalse :
      schedulerCostIsEpistemicAuthority ≡ false
    consumerSetUniquelyDeterminesWholeHiddenWorld : Bool
    consumerSetUniquelyDeterminesWholeHiddenWorldIsFalse :
      consumerSetUniquelyDeterminesWholeHiddenWorld ≡ false

canonicalSpacy369AdaptiveConsumerProbeSchedulerBoundary :
  Spacy369AdaptiveConsumerProbeSchedulerBoundary
canonicalSpacy369AdaptiveConsumerProbeSchedulerBoundary =
  spacy369AdaptiveConsumerProbeSchedulerBoundary
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
