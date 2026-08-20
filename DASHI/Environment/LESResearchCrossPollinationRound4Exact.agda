module DASHI.Environment.LESResearchCrossPollinationRound4Exact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Round 4 follows the gap map to the remaining theorem-sized formal seams.
-- Unlike a status/receipt-only tranche, the imported modules below contain
-- concrete positive theorems and finite falsifiers for:
--
--   stochastic projected kernels;
--   partial observation / belief-state future safety;
--   identifiability, equifinality and active information value;
--   approximate-intertwiner error composition;
--   adaptive-fidelity safe pruning;
--   time/regime shift and path dependence;
--   shared-source uncertainty;
--   exact dependency closure and selective assimilation reopening;
--   finite hybrid trace safety;
--   bounded Pareto completeness;
--   socio-ecological reactive-agent non-factorability;
--   approval-versus-legitimacy non-factorability.
--
-- Domain-specific model validity remains external.  Closing a formal interface
-- means the theorem shape is now explicit, not that LES has already supplied
-- the hydrology/ecology/economics data needed to inhabit every theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)

import DASHI.Core.AdaptiveFidelityPruningExact as Fidelity
import DASHI.Core.AffectedDependencyClosureExact as Closure
import DASHI.Core.ApproximateIntertwinerCompositionExact as Approx
import DASHI.Core.DeclaredScenarioRobustnessExact as Robustness
import DASHI.Core.FiniteStochasticBisimulationExact as Stochastic
import DASHI.Core.IdentifiabilityActiveInformationExact as Information
import DASHI.Core.PartialObservationBeliefSafetyExact as Partial
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Core
import DASHI.Core.SharedSourceUncertaintyExact as SharedUncertainty
import DASHI.Core.SocioEcologicalFeedbackExact as Social
import DASHI.Core.TemporalValidityPathDependenceExact as Temporal
import DASHI.Environment.AssimilationDependencyReopeningExact as Assimilation
import DASHI.Environment.BoundedParetoCompletenessExact as ParetoComplete
import DASHI.Environment.HybridTraceSafetyExact as HybridTrace
import DASHI.Environment.LESResearchCrossPollinationRound2Exact as Round2
import DASHI.Environment.LESResearchCrossPollinationRound3Exact as Round3
import DASHI.Governance.ApprovalLegitimacyNonfactorabilityExact as Governance

------------------------------------------------------------------------
-- 1. Exact causal abstraction is literally an instance of the generic DASHI
-- intertwiner.  This removes one more application-specific copy of the same
-- commuting-square mathematics.
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
-- 2. Concrete gap-closing witnesses are exported at one LES review surface.
------------------------------------------------------------------------

partialObservationCounterexample : Partial.CurrentObservationTerminalisationDefect
partialObservationCounterexample =
  Partial.canonicalCurrentObservationTerminalisationDefect

stochasticProjectionCounterexample :
  Stochastic.KernelBisimulationDefect Stochastic.demoKernel
stochasticProjectionCounterexample = Stochastic.demoKernelDefect

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

------------------------------------------------------------------------
-- 3. Round-4 status distinguishes formal closure from empirical/numerical work.
------------------------------------------------------------------------

record LESRound4FormalClosureStatus : Set where
  constructor lesRound4FormalClosureStatus
  field
    finiteStochasticKernelBisimulationSurfaceConstructed : Bool
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
    boundedParetoCompletenessTheoremConstructed : Bool
    socioEcologicalReactiveCounterexampleConstructed : Bool
    approvalLegitimacyNonfactorabilityConstructed : Bool

open LESRound4FormalClosureStatus public

canonicalLESRound4FormalClosureStatus : LESRound4FormalClosureStatus
canonicalLESRound4FormalClosureStatus =
  lesRound4FormalClosureStatus
    true true true true true
    true true true true true
    true true true true true

record LESRound4RemainingScientificFrontier : Set where
  constructor lesRound4RemainingScientificFrontier
  field
    learnedBeliefStateCertificationStillEmpirical : Bool
    realProbabilityNormalizationAndMetricValueBoundsStillExternal : Bool
    causalErrorMetricCalibrationStillDomainSpecific : Bool
    realExperimentCostAndOutcomeModelsStillExternal : Bool
    realDistributionShiftDetectionStillExternal : Bool
    crossModelDependenceMagnitudesStillEmpirical : Bool
    continuousFlowReachabilityStillModelSpecific : Bool
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
    true true true true true true
    true true true true true true

round4BuildsOnRound3 : Round3.LESRound3Boundary
round4BuildsOnRound3 = Round3.canonicalLESRound3Boundary
