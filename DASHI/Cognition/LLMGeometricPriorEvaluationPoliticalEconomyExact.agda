module DASHI.Cognition.LLMGeometricPriorEvaluationPoliticalEconomyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- LLM EVALUATION, GEOMETRIC PRIORS, AND POLITICAL-ECONOMY INTERPRETATION
--
-- Repo-native donor idea (from the geometric-reasoning / teleodynamics lanes):
-- a semantic transformation should be tested as a structured action with
-- composition/orientation/nuisance/future-learning diagnostics.  "Opposite" is
-- therefore not assumed to mean a literal geometric negation in latent space.
-- E8/Leech/Monster are candidate prior/action families, not an automatic
-- ontology or mechanism.
------------------------------------------------------------------------

data EvaluationDiagnostic : Set where
  pairAccuracyDiagnostic : EvaluationDiagnostic
  compositionOrientationDiagnostic : EvaluationDiagnostic
  nuisanceInvarianceDiagnostic : EvaluationDiagnostic
  futureLearningDiagnostic : EvaluationDiagnostic
  dataEfficiencyDiagnostic : EvaluationDiagnostic
  heldOutTransformationDiagnostic : EvaluationDiagnostic
  residualCompressionDiagnostic : EvaluationDiagnostic

data BenchmarkFinding : Set where
  benchmarkSaturation : BenchmarkFinding
  contaminationInflation : BenchmarkFinding
  expertCurationExtendsLongevity : BenchmarkFinding
  difficultClosedEndedBenchmark : BenchmarkFinding
  capabilityMechanismGap : BenchmarkFinding

record SemanticOppositeBoundary : Set where
  constructor semantic-opposite-boundary
  field
    semanticOppositeIsNotGeometricNegation : Bool
    oppositeActionNeedsRecognitionWitness : Bool
    compositionMustBeChecked : Bool
    orientationMustBeChecked : Bool
    involutionMustBeCheckedWhenClaimed : Bool
    latentDistanceAloneSufficient : Bool
open SemanticOppositeBoundary public

canonicalSemanticOppositeBoundary : SemanticOppositeBoundary
canonicalSemanticOppositeBoundary =
  semantic-opposite-boundary true true true true true false

record PriorInternalisationEvaluation : Set where
  constructor prior-internalisation-evaluation
  field
    pairAccuracyIncluded : Bool
    compositionOrientationIncluded : Bool
    nuisanceInvarianceIncluded : Bool
    futureLearningIncluded : Bool
    dataEfficiencyIncluded : Bool
    heldOutTransformationsIncluded : Bool
    candidatePriorFamilyCompared : Bool
    currentFitDeterminesFutureLanguage : Bool
open PriorInternalisationEvaluation public

preferredPriorInternalisationEvaluation : PriorInternalisationEvaluation
preferredPriorInternalisationEvaluation = prior-internalisation-evaluation
  true true true true true true true false

------------------------------------------------------------------------
-- 2025-26 benchmark evidence is bounded to evaluation failure modes.
------------------------------------------------------------------------

record BenchmarkEvidenceStatus : Set where
  constructor benchmark-evidence-status
  field
    saturationObservedAcrossManyBenchmarks : Bool
    contaminationCanInflateAbsoluteScores : Bool
    benchmarkScoreEqualsMechanisticUnderstanding : Bool
    benchmarkScoreEqualsInternalisedPrior : Bool
    expertCurationCanImproveDurability : Bool
open BenchmarkEvidenceStatus public

currentBenchmarkEvidenceStatus : BenchmarkEvidenceStatus
currentBenchmarkEvidenceStatus = benchmark-evidence-status
  true true false false true

------------------------------------------------------------------------
-- POLITICAL-ECONOMY HYPOTHESIS
--
-- Existing repo capital-recovery work motivates a testable hypothesis that
-- benchmark-visible capability can carry financing/valuation/market-signalling
-- value.  This module deliberately does not infer actor motive from that
-- incentive structure.
------------------------------------------------------------------------

record EvaluationPoliticalEconomyHypothesis : Set where
  constructor evaluation-political-economy-hypothesis
  field
    benchmarkVisibilityHasMarketSignallingValue : Bool
    headlineFriendlyScalarMetricsCanBeSelectedFor : Bool
    benchmarkOptimisationMayDivergeFromPriorInternalisation : Bool
    headlineCapitalMotiveEstablished : Bool
    actorIntentEstablished : Bool
    causalShareOfBenchmarkDesignEstablished : Bool
open EvaluationPoliticalEconomyHypothesis public

steelmanPoliticalEconomyHypothesis : EvaluationPoliticalEconomyHypothesis
steelmanPoliticalEconomyHypothesis = evaluation-political-economy-hypothesis
  true true true false false false

------------------------------------------------------------------------
-- PROMOTION FIREWALLS
------------------------------------------------------------------------

data BenchmarkSuccessEstablishesInternalisedPrior : Set where
data CapitalPressureExplainsBenchmarkChoice : Set where
data BenchmarkSaturationRefutesAllEvaluation : Set where
data E8LeechPriorFitEstablishesHumanLanguageMechanism : Set where
data ChomskyPriorEqualsExceptionalGeometry : Set where

benchmarkSuccessDoesNotEstablishInternalisedPrior :
  BenchmarkSuccessEstablishesInternalisedPrior → ⊥
benchmarkSuccessDoesNotEstablishInternalisedPrior ()

capitalPressureDoesNotByItselfExplainBenchmarkChoice :
  CapitalPressureExplainsBenchmarkChoice → ⊥
capitalPressureDoesNotByItselfExplainBenchmarkChoice ()

benchmarkSaturationDoesNotRefuteAllEvaluation :
  BenchmarkSaturationRefutesAllEvaluation → ⊥
benchmarkSaturationDoesNotRefuteAllEvaluation ()

e8LeechFitDoesNotEstablishHumanLanguageMechanism :
  E8LeechPriorFitEstablishesHumanLanguageMechanism → ⊥
e8LeechFitDoesNotEstablishHumanLanguageMechanism ()

chomskyPriorDoesNotEqualExceptionalGeometry :
  ChomskyPriorEqualsExceptionalGeometry → ⊥
chomskyPriorDoesNotEqualExceptionalGeometry ()

record SteelmanEvaluationBoundary : Set where
  constructor steelman-evaluation-boundary
  field
    scalarBenchmarkPerformanceInsufficient : Bool
    semanticActionTestingRequiredForStrongInternalisationClaim : Bool
    dataEfficiencyRelevantToHumanLearningComparison : Bool
    futureLearningRelevant : Bool
    candidatePriorsShouldBeHeldOutCompared : Bool
    benchmarkIncentivesCanBeStudiedStructurally : Bool
    capitalMotiveCanBeAssertedWithoutEvidence : Bool

canonicalSteelmanEvaluationBoundary : SteelmanEvaluationBoundary
canonicalSteelmanEvaluationBoundary =
  steelman-evaluation-boundary true true true true true true false
