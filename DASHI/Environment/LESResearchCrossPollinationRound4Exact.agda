module DASHI.Environment.LESResearchCrossPollinationRound4Exact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Round 4 follows the gap map to the remaining theorem-sized formal seams.
-- Unlike a status/receipt-only tranche, the imported modules below contain
-- concrete positive theorems and finite falsifiers for stochastic transition
-- quotients, partial observation, identifiability, active information value,
-- approximate abstraction, adaptive fidelity, temporal shift/hysteresis,
-- shared-source uncertainty, exact dependency closure, dense/hybrid time,
-- bounded Pareto completeness, plural preferences, reactive agents and
-- governance legitimacy.  Existing repository policy-relative safety and
-- query-factorisation cores are reused rather than reimplemented.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (_×_; _,_)

import DASHI.Core.AdaptiveFidelityPruningExact as Fidelity
import DASHI.Core.AffectedDependencyClosureExact as Closure
import DASHI.Core.ApproximateIntertwinerCompositionExact as Approx
import DASHI.Core.DeclaredScenarioRobustnessExact as Robustness
import DASHI.Core.FiniteStochasticBisimulationExact as Stochastic
import DASHI.Core.FiniteStochasticRewardPreservationExact as StochasticReward
import DASHI.Core.IdentifiabilityActiveInformationExact as Information
import DASHI.Core.PartialObservationBeliefSafetyExact as Partial
import DASHI.Core.PluralPreferenceNonCollapseExact as Preference
import DASHI.Core.PolicyRelativeProjectionSafety as Policy
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Core
import DASHI.Core.SharedSourceUncertaintyExact as SharedUncertainty
import DASHI.Core.SocioEcologicalFeedbackExact as Social
import DASHI.Core.TemporalValidityPathDependenceExact as Temporal
import DASHI.Environment.AssimilationDependencyReopeningExact as Assimilation
import DASHI.Environment.BoundedParetoCompletenessExact as ParetoComplete
import DASHI.Environment.DenseTimeHybridSemigroupExact as DenseHybrid
import DASHI.Environment.HybridTraceSafetyExact as HybridTrace
import DASHI.Environment.LESResearchCrossPollinationRound2Exact as Round2
import DASHI.Environment.LESResearchCrossPollinationRound3Exact as Round3
import DASHI.Environment.TaskFactorisationQuerySufficiencyBridgeExact as TaskQuery
import DASHI.Governance.ApprovalLegitimacyNonfactorabilityExact as Governance

------------------------------------------------------------------------
-- Exact causal abstraction is an instance of the generic DASHI intertwiner.
------------------------------------------------------------------------

causalAbstractionToGenericIntertwiner :
  ∀ {LowState HighState LowIntervention HighIntervention
      LowOutcome HighOutcome}
    {low : Round2.CausalInterventionSystem LowState LowIntervention LowOutcome}
    {high : Round2.CausalInterventionSystem HighState HighIntervention HighOutcome}
    (abstraction : Round2.ExactCausalAbstraction low high)
    (intervention : LowIntervention) →
  Core.Intertwiner
    (Round2.stateMap abstraction)
    (Round2.stateMap abstraction)
    (Round2.intervene low intervention)
    (Round2.intervene high (Round2.interventionMap abstraction intervention))
causalAbstractionToGenericIntertwiner abstraction intervention =
  Core.intertwiner
    (Round2.interventionSquareCommutes abstraction intervention)

------------------------------------------------------------------------
-- Round 2's robustness witness is stronger than the intended ensemble-relative
-- reading.  It nevertheless induces the correctly quantified declared version.
------------------------------------------------------------------------

round2RobustnessImpliesDeclaredRobustness :
  ∀ {Plan : Set}
    {plan : Plan} →
  (robust : Round2.RobustAcross Plan plan) →
  Robustness.RobustOnDeclared
    (λ candidate future →
      Round2.ScenarioEvaluation.plan (Round2.evaluate robust future) ≡ candidate
      × (Round2.ScenarioEvaluation.acceptable (Round2.evaluate robust future) ≡ true))
    plan
    (Round2.ensemble robust)
round2RobustnessImpliesDeclaredRobustness robust =
  Robustness.robustOnDeclared λ future member →
    Round2.evaluationIsForPlan robust future ,
    Round2.allDeclaredFuturesAcceptable robust future

------------------------------------------------------------------------
-- Existing policy-relative safety is strictly weaker than unrestricted dynamic
-- safety in general; retain the repository's finite witness as an LES design
-- constraint so expensive compression need only be justified for the declared
-- action language/policy when that is genuinely the consumer contract.
------------------------------------------------------------------------

policySafeButNotGloballyDynamicWitness :
  Policy.PolicySafeButNotDynamicallySafeWitness
policySafeButNotGloballyDynamicWitness =
  Policy.canonicalPolicySafeButNotDynamicallySafeWitness

------------------------------------------------------------------------
-- Concrete gap-closing witnesses at one review surface.
------------------------------------------------------------------------

partialObservationCounterexample : Partial.CurrentObservationTerminalisationDefect
partialObservationCounterexample =
  Partial.canonicalCurrentObservationTerminalisationDefect

stochasticProjectionCounterexample :
  Stochastic.KernelBisimulationDefect Stochastic.demoKernel
stochasticProjectionCounterexample = Stochastic.demoKernelDefect

stochasticRewardBoundaryRecorded : StochasticReward.StochasticRewardBoundary
stochasticRewardBoundaryRecorded = StochasticReward.canonicalStochasticRewardBoundary

positiveInformationValueWitness : Information.PositiveDecisionValueWitness
positiveInformationValueWitness = Information.canonicalPositiveDecisionValueWitness

timeErasureCalibrationCounterexample :
  Core.ConsumerDescentDefect Temporal.inputOf Temporal.targetOf
timeErasureCalibrationCounterexample = Temporal.timeErasureCalibrationDefect

pathDependenceCounterexample :
  Core.ConsumerDescentDefect Temporal.forgetHistory Temporal.fineResponse
pathDependenceCounterexample =
  Temporal.fineOutcomeDoesNotDescendThroughPresentState

sharedSourceUncertaintyWitness :
  SharedUncertainty.SharedSourcePair
    SharedUncertainty.erosionDEM SharedUncertainty.machineryDEM
sharedSourceUncertaintyWitness = SharedUncertainty.canonicalSharedDEMPair

assimilationReopensDependentPlan :
  Closure.ReopeningObligation
    Assimilation.Depends
    Assimilation.newObservation
    Assimilation.candidatePlan
assimilationReopensDependentPlan = Assimilation.observationReopensPlan

staticSocioEcologicalProjectionFails :
  Core.ConsumerDescentDefect Social.staticScore (Social.react Social.voluntaryBuffer)
staticSocioEcologicalProjectionFails =
  Social.staticPlanScoreCannotDetermineReactiveOutcome

approvalSurfaceDoesNotDetermineLegitimacy :
  Core.ConsumerDescentDefect
    Governance.approvalProjection Governance.legitimacy
approvalSurfaceDoesNotDetermineLegitimacy =
  Governance.approvalCannotDetermineLegitimacy

preferenceNonCollapseRecorded : Preference.PreferenceNonCollapseBoundary
preferenceNonCollapseRecorded = Preference.canonicalPreferenceNonCollapseBoundary

denseTimeHybridBoundaryRecorded : DenseHybrid.DenseTimeHybridBoundary
denseTimeHybridBoundaryRecorded = DenseHybrid.canonicalDenseTimeHybridBoundary

------------------------------------------------------------------------
-- Formal closure status versus scientific/numerical frontier.
------------------------------------------------------------------------

record LESRound4FormalClosureStatus : Set where
  constructor lesRound4FormalClosureStatus
  field
    finiteStochasticKernelBisimulationSurfaceConstructed : Bool
    finiteStochasticNormalizationConstructed : Bool
    oneStepProjectedRewardPreservationConstructed : Bool
    partialObservationBeliefFutureTheoremConstructed : Bool
    equifinalitySplitterTheoremConstructed : Bool
    activeInformationDecisionValueWitnessConstructed : Bool
    approximateIntertwinerCompositionBoundConstructed : Bool
    adaptiveFidelitySafePruningTheoremConstructed : Bool
    timeShiftCalibrationNonDescentConstructed : Bool
    pathDependenceNonDescentConstructed : Bool
    sharedSourceUncertaintyCounterexampleConstructed : Bool
    exactDependencyClosureConstructed : Bool
    selectiveAssimilationReopeningExampleConstructed : Bool
    finiteHybridTraceSafetyConstructed : Bool
    denseTimeSemigroupConstructed : Bool
    boundedParetoCompletenessTheoremConstructed : Bool
    pluralPreferenceNonCollapseConstructed : Bool
    socioEcologicalReactiveCounterexampleConstructed : Bool
    approvalLegitimacyNonfactorabilityConstructed : Bool
    declaredScenarioRobustnessConstructed : Bool
    policyRelativeSafetyReuseRecorded : Bool
    taskFactorisationQueryCoreReuseRecorded : Bool

open LESRound4FormalClosureStatus public

canonicalLESRound4FormalClosureStatus : LESRound4FormalClosureStatus
canonicalLESRound4FormalClosureStatus =
  lesRound4FormalClosureStatus
    true true true true true true true true true true true
    true true true true true true true true true true true

record LESRound4RemainingScientificFrontier : Set where
  constructor lesRound4RemainingScientificFrontier
  field
    learnedBeliefStateCertificationStillEmpirical : Bool
    realTransitionProbabilitiesStillNeedScientificEstimation : Bool
    discountedOptimalValueBoundsStillNotConstructed : Bool
    causalErrorMetricCalibrationStillDomainSpecific : Bool
    realExperimentCostAndOutcomeModelsStillExternal : Bool
    realDistributionShiftDetectionStillExternal : Bool
    crossModelDependenceMagnitudesStillEmpirical : Bool
    realContinuousFlowLawStillModelSpecific : Bool
    scenarioDiscoveryStillAlgorithmicExternalWork : Bool
    stakeholderPreferenceAcquisitionStillEmpiricalGovernanceWork : Bool
    interventionGrammarMustStillBeDeclaredAndEnumerated : Bool
    reactiveActorModelCalibrationStillEmpirical : Bool
    legitimacyConstitutionStillCannotBeManufacturedByFormalProof : Bool

open LESRound4RemainingScientificFrontier public

canonicalLESRound4RemainingScientificFrontier :
  LESRound4RemainingScientificFrontier
canonicalLESRound4RemainingScientificFrontier =
  lesRound4RemainingScientificFrontier
    true true true true true true true
    true true true true true true

round4BuildsOnRound3 : Round3.LESRound3Boundary
round4BuildsOnRound3 = Round3.canonicalLESRound3Boundary
