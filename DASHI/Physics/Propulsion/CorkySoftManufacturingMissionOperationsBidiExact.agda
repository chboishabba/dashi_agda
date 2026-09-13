{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.CorkySoftManufacturingMissionOperationsBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Planning.CorkySoftOperationalPatternAtlasExact as Corky
import DASHI.Physics.Propulsion.QualifiedHotSectionManufacturingBidiExact as Qual
import DASHI.Physics.Propulsion.JetEngineCanonicalMissionEnergyBidiExact as Mission

------------------------------------------------------------------------
-- CORKYSOFT -> MANUFACTURING -> INSTALLED PART -> MISSION OPERATIONS
--
-- CorkySoft contributes an operational execution grammar, not engine physics:
-- plan/execution separation, custody/handoffs, shortage/readiness, governed
-- substitution, telemetry-vs-reality, exception repair, reconciliation history,
-- and bounded reviewed adaptation.  This owner transports those patterns into
-- the propulsion/manufacturing lane without importing removals business rules
-- as aerospace or semiconductor theorem authority.
------------------------------------------------------------------------

record CorkySoftOperationalSource : Set where
  constructor corkysoft-operational-source
  field
    repository : String
    document : String
    boundedRole : String

open CorkySoftOperationalSource public

inventoryExecutionSource : CorkySoftOperationalSource
inventoryExecutionSource =
  corkysoft-operational-source
    "chboishabba/corkysoft"
    "docs/inventory_execution_workflow.md"
    "Plan-vs-execution, custody/handoff, shortage, readiness, governed substitution and exception calibration."

adaptiveLearningSource : CorkySoftOperationalSource
adaptiveLearningSource =
  corkysoft-operational-source
    "chboishabba/corkysoft"
    "docs/adaptive_learning_loop.md"
    "Bounded proposal/review/apply adaptation from realised outcomes; not permission for silent acceptance-criterion drift."

reconciliationSource : CorkySoftOperationalSource
reconciliationSource =
  corkysoft-operational-source
    "chboishabba/corkysoft"
    "docs/job_cost_and_invoice_reconciliation.md"
    "Required-vs-utilised and execution-vs-later-reconciliation clocks; operational truth remains distinct from planned or accounting surfaces."

routeLoadSource : CorkySoftOperationalSource
routeLoadSource =
  corkysoft-operational-source
    "chboishabba/corkysoft"
    "docs/multi_truck_route_load_optimization.md"
    "Capacity-constrained assignment/sequencing/transfer/repair pattern with explicit transfer eligibility and explainability requirements."

------------------------------------------------------------------------
-- Canonical operational state.  A qualified part or process can exist without
-- being available, installed, serviceable, or used in a realised mission.
------------------------------------------------------------------------

data OperationalAvailability : Set where
  plannedAvailable : OperationalAvailability
  physicallyAvailable : OperationalAvailability
  installedAvailable : OperationalAvailability
  quarantinedUnavailable : OperationalAvailability
  exceptionUnavailable : OperationalAvailability

record QualifiedObjectOperationalState : Set where
  constructor qualified-object-operational-state
  field
    qualification : Qual.QualificationPayment
    availability : OperationalAvailability
    custodyReference : String
    installationReference : String
    serviceabilityReference : String
    sameQualifiedObject : Bool
    sameQualifiedObjectIsTrue : sameQualifiedObject ≡ true

open QualifiedObjectOperationalState public

------------------------------------------------------------------------
-- Handoffs are append-only operational evidence.  Allocation or planning does
-- not create physical custody or installation identity.
------------------------------------------------------------------------

data OperationalHandoffKind : Set where
  manufactureToStores : OperationalHandoffKind
  storesToInspection : OperationalHandoffKind
  inspectionToAssembly : OperationalHandoffKind
  assemblyToEngine : OperationalHandoffKind
  engineToAircraft : OperationalHandoffKind
  aircraftToMission : OperationalHandoffKind
  missionToMaintenance : OperationalHandoffKind
  maintenanceToStores : OperationalHandoffKind
  quarantineHandoff : OperationalHandoffKind

record QualifiedObjectHandoff : Set where
  constructor qualified-object-handoff
  field
    kind : OperationalHandoffKind
    objectIdentity : String
    fromCustody : String
    toCustody : String
    actorReference : String
    timeReference : String
    evidenceReference : String

open QualifiedObjectHandoff public

------------------------------------------------------------------------
-- Readiness and substitution.  A replacement part/process is not silently the
-- same object, and a substitution request is distinct from approval.
------------------------------------------------------------------------

data ReadinessState : Set where
  readyAsPlanned : ReadinessState
  shortageBlocking : ReadinessState
  substitutionReviewRequired : ReadinessState
  approvedSubstitutionReady : ReadinessState
  quarantined : ReadinessState

record SubstitutionProposal : Set where
  constructor substitution-proposal
  field
    originalObject : String
    proposedSubstitute : String
    reason : String
    requester : String
    functionallyEquivalentClaimed : Bool

record SubstitutionApproval : Set where
  constructor substitution-approval
  field
    proposal : SubstitutionProposal
    approver : String
    acceptanceBasis : String
    boundedUse : String
    approved : Bool
    approvedIsTrue : approved ≡ true

open SubstitutionProposal public
open SubstitutionApproval public

------------------------------------------------------------------------
-- Same-mission operational weld.  Mission payment depends on the realised
-- installed/configured object set, not merely the planned bill of materials.
------------------------------------------------------------------------

record OperationalConfigurationMissionWeld : Set where
  constructor operational-configuration-mission-weld
  field
    operationalState : QualifiedObjectOperationalState
    missionPayment : Mission.MissionEnergyPayment
    installedObjectUsedOnSameMission : Bool
    installedObjectUsedOnSameMissionIsTrue :
      installedObjectUsedOnSameMission ≡ true
    missionConfigurationReference : String
    executionEvidenceReference : String

open OperationalConfigurationMissionWeld public

------------------------------------------------------------------------
-- Realised-operation feedback and bounded revision.  Observed mission or
-- maintenance outcomes may propose inspection/process/envelope changes, but a
-- proposal cannot silently rewrite qualification acceptance criteria.
------------------------------------------------------------------------

data FeedbackKind : Set where
  missionPerformanceFeedback : FeedbackKind
  maintenanceFindingFeedback : FeedbackKind
  inspectionEscapeFeedback : FeedbackKind
  shortageSubstitutionFeedback : FeedbackKind
  supplierLotFeedback : FeedbackKind

record OperationalFeedback : Set where
  constructor operational-feedback
  field
    kind : FeedbackKind
    objectOrLotReference : String
    observedOutcome : String
    sourceEvidence : String

record QualificationRevisionProposal : Set where
  constructor qualification-revision-proposal
  field
    feedback : OperationalFeedback
    proposedChange : String
    boundedChange : Bool
    boundedChangeIsTrue : boundedChange ≡ true
    reviewRequired : Bool
    reviewRequiredIsTrue : reviewRequired ≡ true

open OperationalFeedback public
open QualificationRevisionProposal public

------------------------------------------------------------------------
-- Existing CorkySoft atlas anchor.
------------------------------------------------------------------------

corkySoftPatternBoundary : Corky.CorkySoftOperationalPatternBoundary
corkySoftPatternBoundary = Corky.canonicalCorkySoftOperationalPatternBoundary

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data PlannedAllocationImpliesPhysicalCustodyPermission : Set where

data QualifiedPartImpliesInstalledAvailablePermission : Set where

data MatchingPartNumberImpliesSameOperationalObjectPermission : Set where

data SubstitutionRequestImpliesApprovalPermission : Set where

data TelemetryImpliesPhysicalTruthPermission : Set where

data SingleMissionOutcomeRewritesQualificationPermission : Set where

data ReconciledCostImpliesPhysicalUsagePermission : Set where

data LocalOperationalFeasibilityImpliesFleetFeasibilityPermission : Set where

plannedAllocationDoesNotCreatePhysicalCustody :
  PlannedAllocationImpliesPhysicalCustodyPermission → ⊥
plannedAllocationDoesNotCreatePhysicalCustody ()

qualificationDoesNotCreateInstalledAvailability :
  QualifiedPartImpliesInstalledAvailablePermission → ⊥
qualificationDoesNotCreateInstalledAvailability ()

matchingPartNumberDoesNotCreateOperationalIdentity :
  MatchingPartNumberImpliesSameOperationalObjectPermission → ⊥
matchingPartNumberDoesNotCreateOperationalIdentity ()

substitutionRequestDoesNotApproveSubstitution :
  SubstitutionRequestImpliesApprovalPermission → ⊥
substitutionRequestDoesNotApproveSubstitution ()

telemetryDoesNotEqualPhysicalTruth :
  TelemetryImpliesPhysicalTruthPermission → ⊥
telemetryDoesNotEqualPhysicalTruth ()

singleMissionOutcomeDoesNotRewriteQualification :
  SingleMissionOutcomeRewritesQualificationPermission → ⊥
singleMissionOutcomeDoesNotRewriteQualification ()

reconciledCostDoesNotCreatePhysicalUsage :
  ReconciledCostImpliesPhysicalUsagePermission → ⊥
reconciledCostDoesNotCreatePhysicalUsage ()

localOperationalFeasibilityDoesNotProveFleetFeasibility :
  LocalOperationalFeasibilityImpliesFleetFeasibilityPermission → ⊥
localOperationalFeasibilityDoesNotProveFleetFeasibility ()

------------------------------------------------------------------------
-- Reverse acquisition frontier.
------------------------------------------------------------------------

data OperationsReverseTarget : Set where
  acquirePhysicalCustodyHistory : OperationsReverseTarget
  acquireInstalledConfiguration : OperationsReverseTarget
  acquireServiceabilityState : OperationsReverseTarget
  acquireShortageAndSubstitutionHistory : OperationsReverseTarget
  acquireMissionConfigurationUsage : OperationsReverseTarget
  acquireMaintenanceFindings : OperationsReverseTarget
  acquireTelemetryPhysicalTruthReconciliation : OperationsReverseTarget
  acquireLotSupplierRevisionHistory : OperationsReverseTarget
  acquireApprovedQualificationRevision : OperationsReverseTarget

record OperationsReverseObligation : Set where
  constructor operations-reverse-obligation
  field
    target : OperationsReverseTarget
    preferredEvidence : String
    promotes : String
    cannotPromote : String

open OperationsReverseObligation public

record CorkySoftManufacturingMissionOperationsBoundary : Set where
  constructor corkysoft-manufacturing-mission-operations-boundary
  field
    planDistinctFromExecution : Bool
    planDistinctFromExecutionIsTrue : planDistinctFromExecution ≡ true
    qualificationDistinctFromAvailability : Bool
    qualificationDistinctFromAvailabilityIsTrue : qualificationDistinctFromAvailability ≡ true
    substitutionGoverned : Bool
    substitutionGovernedIsTrue : substitutionGoverned ≡ true
    adaptationReviewedAndBounded : Bool
    adaptationReviewedAndBoundedIsTrue : adaptationReviewedAndBounded ≡ true
    corkySoftBusinessRulesBecomeAerospaceTheorems : Bool
    corkySoftBusinessRulesBecomeAerospaceTheoremsIsFalse :
      corkySoftBusinessRulesBecomeAerospaceTheorems ≡ false

canonicalCorkySoftManufacturingMissionOperationsBoundary :
  CorkySoftManufacturingMissionOperationsBoundary
canonicalCorkySoftManufacturingMissionOperationsBoundary =
  corkysoft-manufacturing-mission-operations-boundary
    true refl true refl true refl true refl false refl
