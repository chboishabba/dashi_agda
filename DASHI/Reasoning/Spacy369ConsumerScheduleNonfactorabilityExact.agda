module DASHI.Reasoning.Spacy369ConsumerScheduleNonfactorabilityExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Reasoning.SpacyDependencyToCandidateLogicalPNFExact as Candidate
import DASHI.Reasoning.SpacyNegatedCoordinationScopeTraceExact as Trace
import DASHI.Reasoning.Spacy369AdaptiveConsumerProbeSchedulerExact as Scheduler

------------------------------------------------------------------------
-- CONSUMER / SCHEDULER NON-FACTORABILITY OVER THE SAME MATERIALISED PARSER
-- EVIDENCE.
--
-- The forward parser surface does not determine the backward information plan:
-- the declared consumer bundle is an additional coordinate.  Conversely, the
-- selected plan does not recover the consumer bundle because distinct consumers
-- may legitimately share one probe.
------------------------------------------------------------------------

materialisedSurface : Scheduler.ConsumerBundle → Candidate.CandidateSemanticFragment
materialisedSurface bundle = Trace.negNarrowCandidate

selectedPlan : Scheduler.ConsumerBundle → Scheduler.ScheduledPlan
selectedPlan = Scheduler.schedule

operationalAndFullParserCollision :
  materialisedSurface Scheduler.operationalOnly
  ≡ materialisedSurface Scheduler.subjectStandingAndClosure
operationalAndFullParserCollision = refl

operationalAndFullPlansDiffer :
  selectedPlan Scheduler.operationalOnly
  ≡ selectedPlan Scheduler.subjectStandingAndClosure → ⊥
operationalAndFullPlansDiffer ()

parserSurfaceCannotRecoverScheduledPlan :
  INF.FactorsThrough materialisedSurface selectedPlan → ⊥
parserSurfaceCannotRecoverScheduledPlan =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      Scheduler.operationalOnly
      Scheduler.subjectStandingAndClosure
      operationalAndFullParserCollision
      operationalAndFullPlansDiffer)

------------------------------------------------------------------------
-- Dual collision: subject-only and standing-only are different consumer
-- bundles, but the shared context probe serves both.
------------------------------------------------------------------------

subjectAndStandingPlansSame :
  selectedPlan Scheduler.subjectOnly
  ≡ selectedPlan Scheduler.standingOnly
subjectAndStandingPlansSame = refl

subjectAndStandingBundlesDiffer :
  Scheduler.subjectOnly ≡ Scheduler.standingOnly → ⊥
subjectAndStandingBundlesDiffer ()

scheduledPlanCannotRecoverConsumerBundle :
  INF.FactorsThrough selectedPlan (λ bundle → bundle) → ⊥
scheduledPlanCannotRecoverConsumerBundle =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      Scheduler.subjectOnly
      Scheduler.standingOnly
      subjectAndStandingPlansSame
      subjectAndStandingBundlesDiffer)

------------------------------------------------------------------------
-- Joint parser surface + declared consumer bundle is sufficient to reconstruct
-- the scheduler input for this finite fixture.  We do not promote that into a
-- theorem of whole-world identification.
------------------------------------------------------------------------

jointSchedulerInput :
  Scheduler.ConsumerBundle → Candidate.CandidateSemanticFragment × Scheduler.ConsumerBundle
jointSchedulerInput bundle = materialisedSurface bundle , bundle

planFromJointInput :
  Candidate.CandidateSemanticFragment × Scheduler.ConsumerBundle → Scheduler.ScheduledPlan
planFromJointInput pair = selectedPlan (proj₂ pair)

jointInputRecoversSelectedPlan :
  (bundle : Scheduler.ConsumerBundle) →
  planFromJointInput (jointSchedulerInput bundle) ≡ selectedPlan bundle
jointInputRecoversSelectedPlan bundle = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record Spacy369ConsumerScheduleNonfactorabilityBoundary : Set where
  constructor spacy369ConsumerScheduleNonfactorabilityBoundary
  field
    parserEvidenceAloneDeterminesDownstreamProbeSchedule : Bool
    parserEvidenceAloneDeterminesDownstreamProbeScheduleIsFalse :
      parserEvidenceAloneDeterminesDownstreamProbeSchedule ≡ false
    selectedProbeScheduleUniquelyDeterminesConsumerBundle : Bool
    selectedProbeScheduleUniquelyDeterminesConsumerBundleIsFalse :
      selectedProbeScheduleUniquelyDeterminesConsumerBundle ≡ false
    differentConsumersMayShareOneProbe : Bool
    differentConsumersMayShareOneProbeIsTrue :
      differentConsumersMayShareOneProbe ≡ true
    sameParserEvidenceMaySupportDifferentInformationPolicies : Bool
    sameParserEvidenceMaySupportDifferentInformationPoliciesIsTrue :
      sameParserEvidenceMaySupportDifferentInformationPolicies ≡ true
    parserPlusConsumerInputIdentifiesWholeHiddenWorld : Bool
    parserPlusConsumerInputIdentifiesWholeHiddenWorldIsFalse :
      parserPlusConsumerInputIdentifiesWholeHiddenWorld ≡ false

canonicalSpacy369ConsumerScheduleNonfactorabilityBoundary :
  Spacy369ConsumerScheduleNonfactorabilityBoundary
canonicalSpacy369ConsumerScheduleNonfactorabilityBoundary =
  spacy369ConsumerScheduleNonfactorabilityBoundary
    false refl
    false refl
    true refl
    true refl
    false refl
