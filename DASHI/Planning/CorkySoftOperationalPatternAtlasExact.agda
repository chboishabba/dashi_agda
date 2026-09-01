module DASHI.Planning.CorkySoftOperationalPatternAtlasExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Planning.PlanningBIDICapstoneExact as Planning
import DASHI.Planning.NetworkFlowCapacityCongestionExact as Network
import DASHI.Planning.PlanningAdmissibleTransitionBridgeExact as Admission
import DASHI.Planning.ChemicalManufacturingInventoryLogisticsCrossPollinationExact as Chemical
import DASHI.Core.ObservationInterventionTrustFibreExact as Telemetry
import DASHI.Core.GovernedBackwardConsumerRevisionExact as Consumer

------------------------------------------------------------------------
-- CORKYSOFT OPERATIONAL-PATTERN ATLAS
--
-- External calibration sources:
--   chboishabba/corkysoft README.md
--   chboishabba/corkysoft docs/inventory_execution_workflow.md
--
-- CorkySoft is an operational workflow implementation/calibration surface, not
-- mathematical theorem authority.  This atlas names reusable patterns already
-- owned generically by DASHI planning/core and maps them into chemical/logistics
-- planning without importing removals-domain business rules as universal facts.
------------------------------------------------------------------------

record CorkySoftSourceReceipt : Set where
  constructor corkysoft-source-receipt
  field
    repository : String
    document : String
    boundedRole : String

open CorkySoftSourceReceipt public

corkySoftReadmeSource : CorkySoftSourceReceipt
corkySoftReadmeSource =
  corkysoft-source-receipt
    "chboishabba/corkysoft"
    "README.md"
    "Operational lifecycle/workflow calibration: quote -> booking -> dispatch -> live status -> completion, with planner/network/authority surfaces; not theorem authority."

corkySoftInventorySource : CorkySoftSourceReceipt
corkySoftInventorySource =
  corkysoft-source-receipt
    "chboishabba/corkysoft"
    "docs/inventory_execution_workflow.md"
    "Operational inventory/custody calibration: required -> picked -> packed -> loaded -> transit -> delivered/return/exception; shortage and substitution remain explicit and governed."

------------------------------------------------------------------------
-- Reusable operational pattern families.
------------------------------------------------------------------------

data OperationalPattern : Set where
  lifecycleHandoff
  planExecutionSeparation
  physicalCustody
  shortageReadiness
  governedSubstitution
  roleAuthority
  telemetryVsReality
  exceptionReplanning
  reconciliationHistory
  adaptiveUpdateGovernance
  : OperationalPattern

------------------------------------------------------------------------
-- Plan and execution are not one state.
------------------------------------------------------------------------

data PlannedState : Set where plannedReady : PlannedState

data ExecutedState : Set where executedMissing executedReady : ExecutedState

data WorkflowState : Set where planOnly planAndExecution : WorkflowState

plannedSurface : WorkflowState → PlannedState
plannedSurface _ = plannedReady

executedSurface : WorkflowState → ExecutedState
executedSurface planOnly = executedMissing
executedSurface planAndExecution = executedReady

samePlanDifferentExecution :
  plannedSurface planOnly ≡ plannedSurface planAndExecution
samePlanDifferentExecution = refl

executionStillDiffers :
  executedSurface planOnly ≡ executedSurface planAndExecution → ⊥
executionStillDiffers ()

------------------------------------------------------------------------
-- Custody and handoff evidence are additive historical coordinates.
------------------------------------------------------------------------

data CustodyState : Set where
  depotCustody stagedCustody vehicleCustody transitCustody destinationCustody exceptionCustody : CustodyState

data HandoffEvidence : Set where
  noHandoffEvidence recordedHandoffEvidence : HandoffEvidence

record OperationalHandoff : Set where
  constructor operational-handoff
  field
    fromCustody : CustodyState
    toCustody : CustodyState
    evidence : HandoffEvidence
    actorReference : String
    timeReference : String
    provenanceReference : String

------------------------------------------------------------------------
-- Substitution authority is distinct from substitution request.
------------------------------------------------------------------------

data SubstitutionRequest : Set where requestedSubstitution : SubstitutionRequest

data SubstitutionApproval : Set where approvedSubstitution : SubstitutionApproval

data RequestAutomaticallyApprovesSubstitution : Set where

requestDoesNotApproveSubstitution :
  RequestAutomaticallyApprovesSubstitution → ⊥
requestDoesNotApproveSubstitution ()

------------------------------------------------------------------------
-- Existing-owner welds.
------------------------------------------------------------------------

networkBoundary : Network.CoupledNetworkBoundary
networkBoundary = Network.canonicalCoupledNetworkBoundary

planningAdmissionBoundary : Admission.PlanningAdmissibleTransitionBoundary
planningAdmissionBoundary = Admission.canonicalPlanningAdmissibleTransitionBoundary

chemicalLogisticsBoundary : Chemical.ChemicalManufacturingInventoryLogisticsBoundary
chemicalLogisticsBoundary = Chemical.canonicalChemicalManufacturingInventoryLogisticsBoundary

telemetryBoundary : Telemetry.ObservationInterventionTrustBoundary
telemetryBoundary = Telemetry.canonicalObservationInterventionTrustBoundary

consumerRevisionBoundary : Consumer.GovernedBackwardConsumerRevisionBoundary
consumerRevisionBoundary = Consumer.canonicalGovernedBackwardConsumerRevisionBoundary

------------------------------------------------------------------------
-- Cross-domain transfer boundary.
------------------------------------------------------------------------

record CorkySoftOperationalPatternBoundary : Set where
  constructor corkysoft-operational-pattern-boundary
  field
    plannedStateEqualsExecutedState : Bool
    plannedStateEqualsExecutedStateIsFalse : plannedStateEqualsExecutedState ≡ false
    allocationEqualsPhysicalCustody : Bool
    allocationEqualsPhysicalCustodyIsFalse : allocationEqualsPhysicalCustody ≡ false
    substitutionRequestEqualsApproval : Bool
    substitutionRequestEqualsApprovalIsFalse : substitutionRequestEqualsApproval ≡ false
    liveTelemetryEqualsPhysicalTruth : Bool
    liveTelemetryEqualsPhysicalTruthIsFalse : liveTelemetryEqualsPhysicalTruth ≡ false
    localWorkflowSuccessImpliesWholeNetworkFeasibility : Bool
    localWorkflowSuccessImpliesWholeNetworkFeasibilityIsFalse :
      localWorkflowSuccessImpliesWholeNetworkFeasibility ≡ false
    adaptiveUpdateMaySilentlyRewriteAcceptanceCriteria : Bool
    adaptiveUpdateMaySilentlyRewriteAcceptanceCriteriaIsFalse :
      adaptiveUpdateMaySilentlyRewriteAcceptanceCriteria ≡ false
    corkySoftBusinessRuleIsUniversalPlanningTheorem : Bool
    corkySoftBusinessRuleIsUniversalPlanningTheoremIsFalse :
      corkySoftBusinessRuleIsUniversalPlanningTheorem ≡ false
    operationalPatternsAreReusableCalibration : Bool
    operationalPatternsAreReusableCalibrationIsTrue :
      operationalPatternsAreReusableCalibration ≡ true
    reading : String

canonicalCorkySoftOperationalPatternBoundary : CorkySoftOperationalPatternBoundary
canonicalCorkySoftOperationalPatternBoundary =
  corkysoft-operational-pattern-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    "CorkySoft is a concrete workflow calibration surface for DASHI planning: planned demand, execution truth, custody, shortage/readiness, governed substitution, role authority, telemetry, exceptions/replanning, reconciliation history and adaptive updates remain distinct. The reusable structure is cross-pollinated into chemical/logistics planning while CorkySoft-specific business rules remain source-local rather than theorem authority."
