module DASHI.Governance.BoloBoloPairedGovernanceExperimentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- DIRECT FLAT-vs-NESTED GOVERNANCE EXPERIMENT DESIGN.
--
-- The cleanest way to avoid unqualified historical transfer is to compare a
-- globally coupled process with a nested kana/bolo/tega-like routing scheme in
-- the same target context. This module specifies the evidence obligations for
-- such a pilot; it does not assert that the experiment has been run.
------------------------------------------------------------------------

data GovernanceArm : Set where
  flatGlobalConsensusArm : GovernanceArm
  nestedKanaBoloTegaArm : GovernanceArm

data ProcessObservable : Set where
  elapsedMinutes : ProcessObservable
  unresolvedItemCount : ProcessObservable
  tabledItemCount : ProcessObservable
  boundaryCoordinationCount : ProcessObservable
  delegationReportbackCount : ProcessObservable
  participantIssueIncidenceCount : ProcessObservable
  documentedConflictMediationMinutes : ProcessObservable
  completedDecisionCount : ProcessObservable
  peakConcurrentBoundaryDemand : ProcessObservable
  measuredInterfaceCapacity : ProcessObservable
  interfaceBacklogCount : ProcessObservable
  realisedCrossGroupChannelCount : ProcessObservable

record OutcomeVector : Set where
  constructor outcomeVector
  field
    durationMinutes : Nat
    unresolvedItems : Nat
    tabledItems : Nat
    boundaryInteractions : Nat
    delegationReportbacks : Nat
    incidenceEdges : Nat
    mediationMinutes : Nat
    completedDecisions : Nat
    peakBoundaryDemand : Nat
    interfaceCapacity : Nat
    interfaceBacklog : Nat
    realisedCrossGroupChannels : Nat

open OutcomeVector public

------------------------------------------------------------------------
-- Cost mapping is deliberately abstract and must be fixed before outcomes.
------------------------------------------------------------------------

record PredeclaredCostMapping : Set₁ where
  constructor predeclaredCostMapping
  field
    Cost : OutcomeVector → Nat
    mappingLabel : String
    FrozenBeforeOutcomeInspection : Set
    frozenBeforeOutcomeInspectionWitness : FrozenBeforeOutcomeInspection

open PredeclaredCostMapping public

record PairedGovernanceTrialDesign : Set₁ where
  constructor pairedGovernanceTrialDesign
  field
    costMapping : PredeclaredCostMapping

    sameTargetPopulationOrMatchedBlocks : Bool
    issueBatchesMatchedOrRandomized : Bool
    governanceArmAssignmentRandomizedOrCounterbalanced : Bool
    facilitationProtocolControlledOrRecorded : Bool
    technologyAndVenueControlledOrRecorded : Bool
    timeWindowControlledOrRecorded : Bool
    contaminationAndLearningEffectsAddressed : Bool
    attritionAndMissingnessAudited : Bool
    armFidelityAudited : Bool
    documentaryCompletenessAudited : Bool
    interfaceCapacityMeasurementPlanned : Bool
    concurrentBoundaryDemandMeasurementPlanned : Bool
    backlogMeasurementPlanned : Bool
    realisedInteractionTopologyAuditPlanned : Bool
    repeatedFollowupWindowPlanned : Bool
    actorAdaptationMeasurementPlanned : Bool
    institutionalVersionTrackingPlanned : Bool
    analysisPlanFrozenBeforeOutcomeInspection : Bool
    uncertaintyAndSensitivityPlanPredeclared : Bool
    replicationOrProspectiveValidationPlanned : Bool

open PairedGovernanceTrialDesign public

record PairedObservation : Set where
  constructor pairedObservation
  field
    flatOutcome : OutcomeVector
    nestedOutcome : OutcomeVector

open PairedObservation public

record DirectCoordinationComparison
  (mapping : PredeclaredCostMapping)
  (observation : PairedObservation) : Set where
  constructor directCoordinationComparison
  field
    flatCost : Nat
    nestedCost : Nat
    flatCostMatchesMapping : flatCost ≡ Cost mapping (flatOutcome observation)
    nestedCostMatchesMapping : nestedCost ≡ Cost mapping (nestedOutcome observation)

open DirectCoordinationComparison public

record DirectNestedWin
  {mapping : PredeclaredCostMapping}
  {observation : PairedObservation}
  (comparison : DirectCoordinationComparison mapping observation) : Set where
  constructor directNestedWin
  field
    positiveMargin : Nat
    flatExceedsNestedByPositiveMargin :
      flatCost comparison ≡ nestedCost comparison + suc positiveMargin

open DirectNestedWin public

------------------------------------------------------------------------
-- Measurement mapping to the counterfactual theorem and capacity extension.
------------------------------------------------------------------------

record CounterfactualTermMappingPlan : Set where
  constructor counterfactualTermMappingPlan
  field
    removedGlobalCouplingOperationalized : Bool
    boundaryOverheadOperationalized : Bool
    delegationOverheadOperationalized : Bool
    unresolvedDependencyOperationalized : Bool
    retainedLocalWorkComparableAcrossArms : Bool
    interfaceCapacityOperationalized : Bool
    concurrentBoundaryDemandOperationalized : Bool
    backlogOperationalized : Bool
    realisedInteractionTopologyOperationalized : Bool
    measurementDefinitionsFrozenAcrossArms : Bool
    noOutcomeChosenOnlyAfterSeeingArmDifference : Bool

open CounterfactualTermMappingPlan public

canonicalCounterfactualTermMappingPlan : CounterfactualTermMappingPlan
canonicalCounterfactualTermMappingPlan =
  counterfactualTermMappingPlan
    true true true true true
    true true true true
    true true

record PairedExperimentBoundary : Set where
  constructor pairedExperimentBoundary
  field
    sameTargetContextPreferredOverUnqualifiedHistoricalTransfer : Bool
    costMappingMustBeFrozenBeforeOutcomes : Bool
    flatVersusNestedContrastIsPrimaryStructuralComparison : Bool
    experimentMustMeasureFederationOverheadNotOnlyLocalSavings : Bool
    experimentMustMeasureInterfaceDemandCapacityAndBacklog : Bool
    experimentMustAuditRealisedNotOnlyDeclaredTopology : Bool
    longitudinalFollowupNeededForLongRunClaim : Bool
    failedNestedArmIsInformativeFalsification : Bool
    experimentalCoordinationWinCreatesPoliticalLegitimacy : Bool
    experimentalCoordinationWinProvesEcologicalViability : Bool
    onePilotEstablishesUniversalHumanScale : Bool
    historicalOccupyEvidenceStillUsefulForDesignAndExternalValidity : Bool

open PairedExperimentBoundary public

canonicalPairedExperimentBoundary : PairedExperimentBoundary
canonicalPairedExperimentBoundary =
  pairedExperimentBoundary
    true true true true true true true true
    false false false true

canonicalBoloPairedGovernanceExperimentReceipt : GenericReceipt.GenericReceipt
canonicalBoloPairedGovernanceExperimentReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "direct flat-vs-nested adaptive governance experiment design"
    "DASHI.Governance.BoloBoloPairedGovernanceExperimentExact"
    "PairedGovernanceTrialDesign / OutcomeVector / CounterfactualTermMappingPlan / DirectNestedWin / canonicalPairedExperimentBoundary"
    "specifies the shortest direct empirical route to the bolo counterfactual in one target context while adding peak interface demand, measured coordination-interface capacity, backlog and realised interaction topology to the original cost/process observables, plus planned repeated follow-up, actor-adaptation measurement and institutional-version tracking"
    "the experiment has not been run; a one-shot coordination-cost win cannot establish long-run adaptive performance, interface feasibility, legitimacy, ecological viability or universal scale, and historical/comparator evidence remains contextual/design evidence rather than a substitute for target measurements"
    "agda -i . DASHI/Governance/BoloBoloPairedGovernanceExperimentRegression.agda"
