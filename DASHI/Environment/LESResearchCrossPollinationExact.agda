module DASHI.Environment.LESResearchCrossPollinationExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- This module cross-pollinates the LES planning spine with nearby external
-- research formalisms without claiming that the cited papers prove DASHI's
-- exact constructions.  The exact Agda content below is ours; the references
-- identify established mathematical homes from which stronger quantitative
-- instantiations can be borrowed.
--
-- REFERENCES / MOTIVATION
--
-- Norman Ferns, Prakash Panangaden, Doina Precup,
-- "Metrics for Finite Markov Decision Processes", UAI 2004, pp. 162-169.
-- Continuous extension:
-- "Bisimulation Metrics for Continuous Markov Decision Processes",
-- SIAM Journal on Computing 40(6), 2011, pp. 1662-1714.
-- DOI: 10.1137/10080484X.
--
-- Yann Dubois, Benjamin Bloem-Reddy, Karen Ullrich, Chris J. Maddison,
-- "Lossy Compression for Lossless Prediction", NeurIPS 2021.
-- arXiv: 2106.10800.
--
-- Natalia M. Alexandrov, J. E. Dennis Jr., Robert M. Lewis, Virginia Torczon,
-- "A trust-region framework for managing the use of approximation models in
-- optimization", Structural Optimization 15 (1998), 16-23.
-- DOI: 10.1007/BF01197433.
--
-- Maureen C. Kennedy, E. David Ford, Peter Singleton, Mark A. Finney,
-- James K. Agee,
-- "Informed multi-objective decision-making in environmental management using
-- Pareto optimality", Journal of Applied Ecology 45 (2008), 181-192.
-- DOI: 10.1111/j.1365-2664.2007.01367.x.
--
-- Anthony Baez, Wang Zhang, Ziwen Ma, Subhro Das, Lam M. Nguyen, Luca Daniel,
-- "Guaranteeing Conservation Laws with Projection in Physics-Informed Neural
-- Networks", NeurIPS 2024. arXiv: 2410.17445.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.GenericFuturePartitionRefinementExact as Future
import DASHI.Environment.LatentDepthFormalism as Latent
import DASHI.Environment.ParetoPlanning as Pareto
import DASHI.Environment.QuantitiesConservation as Q
import DASHI.Environment.SurrogateCalibration as Surrogate

------------------------------------------------------------------------
-- 1. Exact/approximate behavioural compression.
--
-- `DynamicConsumerSafety` already supplies exact trace congruence.  The
-- following quantitative contract is the deliberately weaker metric analogue:
-- closeness must be propagated by every declared action, not merely observed
-- at the current state.
------------------------------------------------------------------------

record ApproximateFutureMetricContract
    {State Action Observation : Set}
    (observe : State → Observation)
    (step : Action → State → State) : Set₁ where
  constructor approximateFutureMetricContract
  field
    stateDistance : State → State → Nat
    observationDistance : Observation → Observation → Nat
    tolerance : Nat
    currentObservationControlled :
      ∀ {left right} →
      stateDistance left right ≤ tolerance →
      observationDistance (observe left) (observe right) ≤ tolerance
    actionNonexpansiveAtTolerance :
      ∀ action {left right} →
      stateDistance left right ≤ tolerance →
      stateDistance (step action left) (step action right) ≤ tolerance

open ApproximateFutureMetricContract public

traceStateClose :
  ∀ {State Action Observation}
    {observe : State → Observation}
    {step : Action → State → State}
    (contract : ApproximateFutureMetricContract observe step)
    (actions : List Action)
    {left right : State} →
  stateDistance contract left right ≤ tolerance contract →
  stateDistance contract
    (Future.run step actions left)
    (Future.run step actions right)
    ≤ tolerance contract
traceStateClose contract [] close = close
traceStateClose contract (action ∷ rest) close =
  traceStateClose contract rest
    (actionNonexpansiveAtTolerance contract action close)

traceObservationClose :
  ∀ {State Action Observation}
    {observe : State → Observation}
    {step : Action → State → State}
    (contract : ApproximateFutureMetricContract observe step)
    (actions : List Action)
    {left right : State} →
  stateDistance contract left right ≤ tolerance contract →
  observationDistance contract
    (observe (Future.run step actions left))
    (observe (Future.run step actions right))
    ≤ tolerance contract
traceObservationClose contract actions close =
  currentObservationControlled contract
    (traceStateClose contract actions close)

------------------------------------------------------------------------
-- 2. Decision-relevant/task-relative sufficiency.
--
-- This is an exact factorisation criterion: every declared task must factor
-- through the compressed representation.  It is intentionally task-relative;
-- it does not imply DynamicConsumerSafety for undeclared future dynamics.
------------------------------------------------------------------------

record TaskFactorisation
    {State Representation Task Output : Set}
    (project : State → Representation)
    (evaluate : Task → State → Output) : Set₁ where
  constructor taskFactorisation
  field
    evaluateReduced : Task → Representation → Output
    factorises :
      ∀ task state →
      evaluate task state ≡ evaluateReduced task (project state)

open TaskFactorisation public

sameRepresentationSameTaskOutput :
  ∀ {State Representation Task Output}
    {project : State → Representation}
    {evaluate : Task → State → Output}
    (factor : TaskFactorisation project evaluate)
    (task : Task)
    {left right : State} →
  project left ≡ project right →
  evaluate task left ≡ evaluate task right
sameRepresentationSameTaskOutput factor task same
  rewrite factorises factor task left
        | factorises factor task right =
  cong (evaluateReduced factor task) same

------------------------------------------------------------------------
-- 3. Reopenability is an independent admissibility route.
------------------------------------------------------------------------

data CompressionAdmission
    {State Action Observation Task Output : Set}
    (system : DASHI.Core.TypedDependencyCore.DependentActionSystem State Action)
    (project : State → Observation)
    (evaluate : Task → State → Output) : Set₁ where
  dynamicallySafe :
    Dynamic.DynamicConsumerSafety system project →
    CompressionAdmission system project evaluate
  taskSufficientAndReopenable :
    TaskFactorisation project evaluate →
    Dynamic.ReopeningScheme project →
    CompressionAdmission system project evaluate

------------------------------------------------------------------------
-- 4. Multi-fidelity trust-region style escalation boundary.
--
-- LES's A/B/C lane is not assumed to be an ordered mesh hierarchy.  A runtime
-- may use genuinely different model classes.  Consequently the exact formal
-- obligation is to record local agreement evidence and fail closed when that
-- evidence is absent or outside its declared region.
------------------------------------------------------------------------

record FidelityAgreementReceipt : Set where
  constructor fidelityAgreementReceipt
  field
    lowerFidelityModel : String
    higherFidelityModel : String
    comparisonRegion : String
    agreementStatistic : Nat
    agreementThreshold : Nat
    agreementWithinThreshold : agreementStatistic ≤ agreementThreshold
    localConsistencyMethod : String
    comparisonEvidence : List String

open FidelityAgreementReceipt public

record TrustRegionEscalationReceipt : Set where
  constructor trustRegionEscalationReceipt
  field
    startingLane : Latent.ModelLane
    localAgreement : FidelityAgreementReceipt
    surrogateAssessment : Surrogate.SurrogateAssessment
    resultingLane : Latent.ModelLane
    resultingLaneMatches :
      resultingLane ≡
      Latent.chooseLane startingLane
        (Surrogate.assessmentEscalation surrogateAssessment)
    regionUpdateRecorded : Bool
    highFidelityVerificationRecorded : Bool

open TrustRegionEscalationReceipt public

------------------------------------------------------------------------
-- 5. Hard invariant projection.
--
-- A soft penalty or small residual is not a proof that the projected state
-- satisfies a conservation/admissibility law.  This generic carrier requires
-- the projection itself to land in the invariant set.
------------------------------------------------------------------------

record HardInvariantProjection
    {State : Set}
    (Invariant : State → Set) : Set₁ where
  constructor hardInvariantProjection
  field
    project : State → State
    projectedInvariant : ∀ state → Invariant (project state)

open HardInvariantProjection public

record ConservationProjectionReceipt {State : Set} : Set₁ where
  constructor conservationProjectionReceipt
  field
    conservationOf : State → Q.ConservationBundle
    projectState : State → State
    projectedConservation : ∀ state → Q.ConservationBundle
    projectedBundleMatches :
      ∀ state → projectedConservation state ≡ conservationOf (projectState state)
    numericalProjectionMethod : String
    numericalEvidence : List String

open ConservationProjectionReceipt public

------------------------------------------------------------------------
-- 6. Pareto front interpretation remains separate from preference/choice.
------------------------------------------------------------------------

record ParetoInterpretationReceipt : Set where
  constructor paretoInterpretationReceipt
  field
    finiteResult : Pareto.FiniteParetoResult
    frontDistillationMethod : String
    tradeoffsPreservedInReport : Bool
    noUniqueOptimumInferredFromNonDominance : Bool
    decisionPreferenceModelRecordedSeparately : Bool

open ParetoInterpretationReceipt public

------------------------------------------------------------------------
-- 7. Approval is evidence-bearing and action-bound, not a detached Boolean.
------------------------------------------------------------------------

record ApprovalEvent : Set where
  constructor approvalEvent
  field
    governedActionHash : String
    authorityIdentity : String
    authorityRole : String
    recordedAt : String
    scope : String
    evidenceArtifactHash : String
    approved : Bool
    revocationReference : String

open ApprovalEvent public

record DeploymentApprovalWitness (event : ApprovalEvent) : Set where
  constructor deploymentApprovalWitness
  field
    approvalGranted : approved event ≡ true
    scopeChecked : Bool
    authorityCurrent : Bool
    revocationChecked : Bool

open DeploymentApprovalWitness public

------------------------------------------------------------------------
-- 8. Research-frontier boundary.
--
-- These are deliberately *gaps*, not silently asserted capabilities.  The
-- current deterministic/exact LES spine does not by itself discharge them.
------------------------------------------------------------------------

record LESResearchGapBoundary : Set where
  constructor lesResearchGapBoundary
  field
    stochasticTransitionMetricsStillRequired : Bool
    partialObservabilityAndBeliefStateStillRequired : Bool
    causalInterventionPreservationStillRequired : Bool
    structuralIdentifiabilityStillRequired : Bool
    equifinalityAccountingStillRequired : Bool
    deepUncertaintyRobustnessStillRequired : Bool
    nonstationaryDistributionShiftStillRequired : Bool
    valueOfInformationAndActiveSensingStillRequired : Bool
    correlatedCrossModelErrorPropagationStillRequired : Bool
    continuousTimeHybridDynamicsStillRequired : Bool
    pathDependenceAndHysteresisStillRequired : Bool
    preferenceElicitationBeyondParetoStillRequired : Bool
    spatialScaleAndAggregationBiasStillRequired : Bool
    onlineAssimilationAndModelRevisionStillRequired : Bool
    governanceLegitimacyContestabilityAndRevocationStillRequired : Bool

open LESResearchGapBoundary public

canonicalLESResearchGapBoundary : LESResearchGapBoundary
canonicalLESResearchGapBoundary =
  lesResearchGapBoundary
    true true true true true
    true true true true true
    true true true true true

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record LESResearchCrossPollinationBoundary : Set where
  constructor lesResearchCrossPollinationBoundary
  field
    bisimulationLiteratureMotivatesButDoesNotProveOurTraceSafety : Bool
    taskCompressionLiteratureMotivatesButDoesNotProveReopenability : Bool
    trustRegionLiteratureDoesNotMakeABCModelsAutomaticallyOrdered : Bool
    conservationProjectionLiteratureDoesNotValidateExternalModels : Bool
    paretoLiteratureDoesNotSupplyStakeholderPreferences : Bool
    approvalProvenanceDoesNotByItselfEstablishLegitimacy : Bool
    researchGapFieldsAreOpenObligationsNotTheorems : Bool

open LESResearchCrossPollinationBoundary public

canonicalLESResearchCrossPollinationBoundary :
  LESResearchCrossPollinationBoundary
canonicalLESResearchCrossPollinationBoundary =
  lesResearchCrossPollinationBoundary true true true true true true true
