module DASHI.Environment.LESResearchCrossPollinationRound2Exact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Second LES research cross-pollination round.  This module turns five
-- previously named gaps into exact reusable contract surfaces while keeping
-- the numerical/scientific obligations explicit.
--
-- REFERENCES / MOTIVATION
--
-- Sander Beckers, Joseph Y. Halpern,
-- "Abstracting Causal Models", AAAI 2019.
-- See also the exact-transformation programme of Rubenstein et al. for
-- intervention-preserving transformations between causal models.
-- The citations motivate the commuting intervention square below; they do not
-- prove this Agda construction.
--
-- Robert J. Lempert,
-- "Robust Decision Making (RDM)", in Decision Making under Deep Uncertainty,
-- Springer, 2019, pp. 23-51.
-- Marjolijn Haasnoot, Andrew Warren, Jan H. Kwakkel,
-- "Dynamic Adaptive Policy Pathways (DAPP)", ibid., pp. 71-92.
-- DOI for the volume: 10.1007/978-3-030-05252-2.
--
-- Stan Openshaw's modifiable areal unit problem (MAUP) distinguishes scale
-- effects from zoning effects.  The formal contribution here is to express
-- spatial aggregation bias as a failure of descent/intertwining rather than
-- merely a descriptive GIS warning.
--
-- Ensemble Kalman filtering motivates the state-assimilation boundary.  LES's
-- dependency invalidation/reopening layer is deliberately stronger than the
-- filtering update itself: assimilation changes scientific state; dependency
-- closure records which derived consumers must be reconsidered.
--
-- Rajeev Alur, Costas Courcoubetis, Thomas A. Henzinger, Pei-Hsin Ho,
-- "Hybrid Automata: An Algorithmic Approach to the Specification and
-- Verification of Hybrid Systems", Hybrid Systems I, LNCS 736, 1993.
-- Hybrid reachability is generally difficult/undecidable without restrictions;
-- this module therefore records a hybrid execution contract, not a universal
-- decidability claim.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Environment.LESResearchCrossPollinationExact as Round1

------------------------------------------------------------------------
-- 1. Causal abstraction: prediction is weaker than intervention preservation.
------------------------------------------------------------------------

record CausalInterventionSystem
    (State Intervention Outcome : Set) : Set₁ where
  constructor causalInterventionSystem
  field
    intervene : Intervention → State → State
    observeOutcome : State → Outcome

open CausalInterventionSystem public

record ExactCausalAbstraction
    {LowState HighState LowIntervention HighIntervention
     LowOutcome HighOutcome : Set}
    (low : CausalInterventionSystem LowState LowIntervention LowOutcome)
    (high : CausalInterventionSystem HighState HighIntervention HighOutcome)
    : Set₁ where
  constructor exactCausalAbstraction
  field
    stateMap : LowState → HighState
    interventionMap : LowIntervention → HighIntervention
    outcomeMap : LowOutcome → HighOutcome

    interventionSquareCommutes :
      ∀ intervention state →
      stateMap (intervene low intervention state)
      ≡ intervene high (interventionMap intervention) (stateMap state)

    outcomeSquareCommutes :
      ∀ state →
      outcomeMap (observeOutcome low state)
      ≡ observeOutcome high (stateMap state)

open ExactCausalAbstraction public

causalOutcomeCommutesAfterIntervention :
  ∀ {LowState HighState LowIntervention HighIntervention
      LowOutcome HighOutcome}
    {low : CausalInterventionSystem LowState LowIntervention LowOutcome}
    {high : CausalInterventionSystem HighState HighIntervention HighOutcome}
    (abstraction : ExactCausalAbstraction low high)
    (intervention : LowIntervention)
    (state : LowState) →
  outcomeMap abstraction
    (observeOutcome low (intervene low intervention state))
  ≡ observeOutcome high
      (intervene high
        (interventionMap abstraction intervention)
        (stateMap abstraction state))
causalOutcomeCommutesAfterIntervention abstraction intervention state
  rewrite outcomeSquareCommutes abstraction (intervene _ intervention state)
        | interventionSquareCommutes abstraction intervention state = refl

record CausalAbstractionBoundary : Set where
  constructor causalAbstractionBoundary
  field
    predictiveAgreementDoesNotImplyInterventionalAgreement : Bool
    interventionalAgreementDoesNotByItselfSupplyCounterfactualSemantics : Bool
    approximateCausalAbstractionNeedsDeclaredErrorMetric : Bool
    hiddenExogenousStructureMustNotBeSilentlyErased : Bool

open CausalAbstractionBoundary public

canonicalCausalAbstractionBoundary : CausalAbstractionBoundary
canonicalCausalAbstractionBoundary =
  causalAbstractionBoundary true true true true

------------------------------------------------------------------------
-- 2. Deep uncertainty: robustness is a separate axis from model fidelity.
------------------------------------------------------------------------

record PlausibleFuture : Set where
  constructor plausibleFuture
  field
    futureId : String
    assumptions : List String
    provenance : List String
    probabilityClaimed : Bool

open PlausibleFuture public

record ScenarioEvaluation (Plan : Set) : Set where
  constructor scenarioEvaluation
  field
    plan : Plan
    future : PlausibleFuture
    acceptable : Bool
    vulnerabilityReasons : List String
    evidence : List String

open ScenarioEvaluation public

record RobustAcross (Plan : Set) (plan : Plan) : Set₁ where
  constructor robustAcross
  field
    ensemble : List PlausibleFuture
    evaluate : PlausibleFuture → ScenarioEvaluation Plan
    evaluationIsForPlan :
      ∀ future → ScenarioEvaluation.plan (evaluate future) ≡ plan
    acceptanceCriterion : String
    allDeclaredFuturesAcceptable :
      ∀ future → ScenarioEvaluation.acceptable (evaluate future) ≡ true

open RobustAcross public

record ScenarioDiscoveryReceipt (Plan : Set) : Set where
  constructor scenarioDiscoveryReceipt
  field
    candidate : Plan
    sampledFutures : List PlausibleFuture
    vulnerabilityRegionDescription : List String
    discoveryMethod : String
    failedCasesRetained : Bool
    noProbabilityDistributionInferredFromScenarioSet : Bool

open ScenarioDiscoveryReceipt public

record AdaptivePathway (Plan : Set) : Set where
  constructor adaptivePathway
  field
    initialPlan : Plan
    signposts : List String
    triggerConditions : List String
    contingentPlans : List Plan
    adaptationEvidence : List String

open AdaptivePathway public

record DeepUncertaintyBoundary : Set where
  constructor deepUncertaintyBoundary
  field
    highFidelityDoesNotEliminateScenarioUncertainty : Bool
    plausibleFutureSetIsNotAutomaticallyProbabilistic : Bool
    robustnessDoesNotImplyOptimality : Bool
    pathwayTriggerNeedsObservableSignpost : Bool

open DeepUncertaintyBoundary public

canonicalDeepUncertaintyBoundary : DeepUncertaintyBoundary
canonicalDeepUncertaintyBoundary =
  deepUncertaintyBoundary true true true true

------------------------------------------------------------------------
-- 3. MAUP as failure of spatial aggregation descent/intertwining.
------------------------------------------------------------------------

data AggregationChangeKind : Set where
  scaleEffect : AggregationChangeKind
  zoningEffect : AggregationChangeKind

record SpatialAggregation
    (Fine Coarse : Set) : Set₁ where
  constructor spatialAggregation
  field
    aggregate : Fine → Coarse
    changeKind : AggregationChangeKind
    schemeReference : String

open SpatialAggregation public

record AggregationIntertwiner
    {Fine Coarse FineResult CoarseResult : Set}
    (aggregation : SpatialAggregation Fine Coarse)
    (analyseFine : Fine → FineResult)
    (analyseCoarse : Coarse → CoarseResult)
    (aggregateResult : FineResult → CoarseResult) : Set₁ where
  constructor aggregationIntertwiner
  field
    commutes :
      ∀ fine →
      analyseCoarse (aggregate aggregation fine)
      ≡ aggregateResult (analyseFine fine)

open AggregationIntertwiner public

record MAUPDefect
    {Fine Coarse FineResult CoarseResult : Set}
    (aggregation : SpatialAggregation Fine Coarse)
    (analyseFine : Fine → FineResult)
    (analyseCoarse : Coarse → CoarseResult)
    (aggregateResult : FineResult → CoarseResult) : Set₁ where
  constructor maupDefect
  field
    witnessFineState : Fine
    descentFails :
      analyseCoarse (aggregate aggregation witnessFineState)
      ≡ aggregateResult (analyseFine witnessFineState) → ⊥

open MAUPDefect public

maupDefectContradictsIntertwiner :
  ∀ {Fine Coarse FineResult CoarseResult}
    {aggregation : SpatialAggregation Fine Coarse}
    {analyseFine : Fine → FineResult}
    {analyseCoarse : Coarse → CoarseResult}
    {aggregateResult : FineResult → CoarseResult} →
  AggregationIntertwiner aggregation analyseFine analyseCoarse aggregateResult →
  MAUPDefect aggregation analyseFine analyseCoarse aggregateResult →
  ⊥
maupDefectContradictsIntertwiner intertwiner defect =
  descentFails defect (commutes intertwiner (witnessFineState defect))

record SpatialAggregationBoundary : Set where
  constructor spatialAggregationBoundary
  field
    scaleChangeAndRezoningAreDistinctFailureModes : Bool
    coarseMapAgreementDoesNotProveFineConsumerSafety : Bool
    spatialAggregationNeedsConsumerSpecificDescentProof : Bool
    aggregationDefectShouldRemainReopenableToFineCarrier : Bool

open SpatialAggregationBoundary public

canonicalSpatialAggregationBoundary : SpatialAggregationBoundary
canonicalSpatialAggregationBoundary =
  spatialAggregationBoundary true true true true

------------------------------------------------------------------------
-- 4. Data assimilation plus dependency-aware reopening/invalidation.
------------------------------------------------------------------------

record AssimilationUpdate
    (State Evidence : Set) : Set₁ where
  constructor assimilationUpdate
  field
    prior : State
    newEvidence : Evidence
    posterior : State
    updateMethod : String
    updateEvidence : List String

open AssimilationUpdate public

record DependencyInvalidation
    (Artifact : Set) : Set₁ where
  constructor dependencyInvalidation
  field
    changedArtifacts : List Artifact
    affectedClosure : List Artifact
    invalidatedDerivedArtifacts : List Artifact
    retainedUnaffectedArtifacts : List Artifact
    closureMethod : String
    closureEvidence : List String

open DependencyInvalidation public

record AssimilationReplanningReceipt
    (State Evidence Artifact Consumer : Set) : Set₁ where
  constructor assimilationReplanningReceipt
  field
    assimilation : AssimilationUpdate State Evidence
    invalidation : DependencyInvalidation Artifact
    affectedConsumers : List Consumer
    unaffectedConsumers : List Consumer
    reopenedReceipts : List String
    replanOnlyAffectedConsumers : Bool
    provenance : List String

open AssimilationReplanningReceipt public

record AssimilationBoundary : Set where
  constructor assimilationBoundary
  field
    posteriorUpdateDoesNotValidateObservationModel : Bool
    ensembleCovarianceIsNotExactDependencyProvenance : Bool
    stateRevisionMustInvalidateAffectedDerivedClaims : Bool
    unaffectedConsumerRetentionNeedsDependencyJustification : Bool

open AssimilationBoundary public

canonicalAssimilationBoundary : AssimilationBoundary
canonicalAssimilationBoundary =
  assimilationBoundary true true true true

------------------------------------------------------------------------
-- 5. Hybrid discrete/continuous execution contract.
------------------------------------------------------------------------

record HybridSystem
    (Mode Continuous DiscreteAction : Set) : Set₁ where
  constructor hybridSystem
  field
    continuousStep : Mode → Continuous → Continuous
    discreteJump : DiscreteAction → Mode → Continuous → Mode × Continuous
    invariant : Mode → Continuous → Set

open HybridSystem public

data HybridCommand (Mode Continuous DiscreteAction : Set) : Set where
  flow : HybridCommand Mode Continuous DiscreteAction
  jump : DiscreteAction → HybridCommand Mode Continuous DiscreteAction

record HybridState (Mode Continuous : Set) : Set where
  constructor hybridState
  field
    mode : Mode
    continuous : Continuous

open HybridState public

hybridStep :
  ∀ {Mode Continuous DiscreteAction} →
  HybridSystem Mode Continuous DiscreteAction →
  HybridCommand Mode Continuous DiscreteAction →
  HybridState Mode Continuous →
  HybridState Mode Continuous
hybridStep system flow state =
  hybridState
    (mode state)
    (continuousStep system (mode state) (continuous state))
hybridStep system (jump action) state with
  discreteJump system action (mode state) (continuous state)
... | nextMode , nextContinuous = hybridState nextMode nextContinuous

record HybridSafetyWitness
    {Mode Continuous DiscreteAction : Set}
    (system : HybridSystem Mode Continuous DiscreteAction)
    (Safe : HybridState Mode Continuous → Set) : Set₁ where
  constructor hybridSafetyWitness
  field
    initialSafe : ∀ state → Safe state → Safe state
    stepPreservesSafe :
      ∀ command state →
      Safe state → Safe (hybridStep system command state)

open HybridSafetyWitness public

record HybridDynamicsBoundary : Set where
  constructor hybridDynamicsBoundary
  field
    discreteTraceSafetyDoesNotCoverContinuousFlowByItself : Bool
    unrestrictedHybridReachabilityNotClaimedDecidable : Bool
    physicalInvariantMustHoldAcrossFlowAndJump : Bool
    hysteresisNeedsExplicitStateWhenFutureDependsOnHistory : Bool

open HybridDynamicsBoundary public

canonicalHybridDynamicsBoundary : HybridDynamicsBoundary
canonicalHybridDynamicsBoundary =
  hybridDynamicsBoundary true true true true

------------------------------------------------------------------------
-- Round-2 status: these gaps now have contract surfaces, but scientific proof
-- obligations remain.  Having the record type is not the same as exhibiting
-- an LES deployment witness.
------------------------------------------------------------------------

record LESRound2ResearchStatus : Set where
  constructor lesRound2ResearchStatus
  field
    causalAbstractionSurfaceAdded : Bool
    deepUncertaintySurfaceAdded : Bool
    spatialAggregationDescentSurfaceAdded : Bool
    assimilationInvalidationSurfaceAdded : Bool
    hybridDynamicsSurfaceAdded : Bool
    numericalCausalErrorBoundsStillOpen : Bool
    scenarioDiscoveryAlgorithmsStillExternal : Bool
    realGISMAUPCertificatesStillOpen : Bool
    assimilationCalibrationStillExternal : Bool
    decidableHybridFragmentsStillOpen : Bool
    proceduralGovernanceStillOpen : Bool
    socioEcologicalGameDynamicsStillOpen : Bool
    planningSearchCompletenessStillOpen : Bool

open LESRound2ResearchStatus public

canonicalLESRound2ResearchStatus : LESRound2ResearchStatus
canonicalLESRound2ResearchStatus =
  lesRound2ResearchStatus
    true true true true true
    true true true true true
    true true true

round2BuildsOnRound1 : Round1.LESResearchCrossPollinationBoundary
round2BuildsOnRound1 = Round1.canonicalLESResearchCrossPollinationBoundary
