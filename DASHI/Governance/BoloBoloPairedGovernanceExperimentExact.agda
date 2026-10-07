module DASHI.Governance.BoloBoloPairedGovernanceExperimentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- DIRECT FLAT-vs-NESTED GOVERNANCE EXPERIMENT DESIGN.
--
-- The cleanest way to avoid unqualified historical transfer is to compare a
-- globally coupled process with a nested kana/bolo/tega-like routing scheme in
-- the same target context.  This module specifies the evidence obligations for
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

open OutcomeVector public

------------------------------------------------------------------------
-- Cost mapping is deliberately abstract and must be fixed before outcomes.
-- This avoids retrospectively choosing weights that make one arm look better.
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
    analysisPlanFrozenBeforeOutcomeInspection : Bool
    uncertaintyAndSensitivityPlanPredeclared : Bool
    replicationOrProspectiveValidationPlanned : Bool

open PairedGovernanceTrialDesign public

------------------------------------------------------------------------
-- Direct estimand surface.
------------------------------------------------------------------------

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
-- Measurement mapping to the counterfactual theorem.
--
-- These are experiment-design obligations, not automatic identities.  A pilot
-- must specify how observed boundary/delegation/unresolved coordinates map to
-- the theorem's cost components and whether retained local work is comparable.
------------------------------------------------------------------------

record CounterfactualTermMappingPlan : Set where
  constructor counterfactualTermMappingPlan
  field
    removedGlobalCouplingOperationalized : Bool
    boundaryOverheadOperationalized : Bool
    delegationOverheadOperationalized : Bool
    unresolvedDependencyOperationalized : Bool
    retainedLocalWorkComparableAcrossArms : Bool
    measurementDefinitionsFrozenAcrossArms : Bool
    noOutcomeChosenOnlyAfterSeeingArmDifference : Bool

open CounterfactualTermMappingPlan public

canonicalCounterfactualTermMappingPlan : CounterfactualTermMappingPlan
canonicalCounterfactualTermMappingPlan =
  counterfactualTermMappingPlan true true true true true true true

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record PairedExperimentBoundary : Set where
  constructor pairedExperimentBoundary
  field
    sameTargetContextPreferredOverUnqualifiedHistoricalTransfer : Bool
    costMappingMustBeFrozenBeforeOutcomes : Bool
    flatVersusNestedContrastIsPrimaryStructuralComparison : Bool
    experimentMustMeasureFederationOverheadNotOnlyLocalSavings : Bool
    failedNestedArmIsInformativeFalsification : Bool
    experimentalCoordinationWinCreatesPoliticalLegitimacy : Bool
    experimentalCoordinationWinProvesEcologicalViability : Bool
    onePilotEstablishesUniversalHumanScale : Bool
    historicalOccupyEvidenceStillUsefulForDesignAndExternalValidity : Bool

open PairedExperimentBoundary public

canonicalPairedExperimentBoundary : PairedExperimentBoundary
canonicalPairedExperimentBoundary =
  pairedExperimentBoundary
    true
    true
    true
    true
    true
    false
    false
    false
    true

canonicalBoloPairedGovernanceExperimentReceipt : GenericReceipt.GenericReceipt
canonicalBoloPairedGovernanceExperimentReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "direct flat-vs-nested governance experiment design"
    "DASHI.Governance.BoloBoloPairedGovernanceExperimentExact"
    "PairedGovernanceTrialDesign / DirectNestedWin / canonicalPairedExperimentBoundary"
    "specifies the shortest direct empirical route to the bolo counterfactual: compare globally coupled and nested kana-bolo-tega-like decision routing in the same target context with matched/randomized issue exposure, frozen measurement and cost mapping, explicit arm-fidelity/documentary audits, uncertainty planning, and direct measurement of both locality savings and federation overhead"
    "the experiment has not been run; a coordination-cost win would not create legitimacy, ecological viability or universal scale claims, and historical Occupy evidence remains contextual/design evidence rather than a substitute for the target comparison"
    "agda -i . DASHI/Governance/BoloBoloPairedGovernanceExperimentRegression.agda"
