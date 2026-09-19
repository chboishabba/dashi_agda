module DASHI.Interop.SLRProductionRoadmapParityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SLRConsumerRequirementV2Exact as Consumer
import DASHI.Interop.SLRResidualDrivenProducerPlannerExact as Planner
import DASHI.Interop.SLRReviewedEvidencePaymentExact as Review
import DASHI.Interop.SLRBoundedResearchIterationControlExact as Iteration
import DASHI.Interop.SLRWorldModelSuiteConvergenceRoadmapExact as Suite
import DASHI.Interop.SLRGWBPhysicalObjectAcquisitionPolicyExact as Physical
import DASHI.Interop.SLRSprint1AcquisitionMachineExact as Sprint1
import DASHI.Interop.SLRExternalOntologyEnrichmentRouterExact as External

------------------------------------------------------------------------
-- SENSIBLAW / SLR PRODUCTION ROADMAP PARITY
--
-- Production owner:
--   chboishabba/slr
--
-- Golden reference owner:
--   chboishabba/dashi_agda
--
-- SLR is the production SensibLaw runtime.  Agda is the golden semantic and
-- architectural reference.  The historical Python SensibLaw implementation
-- remains useful evidence/reference material but does not own production
-- runtime semantics.
------------------------------------------------------------------------

data RoadmapPhaseState : Set where
  paid : RoadmapPhaseState
  active : RoadmapPhaseState
  next : RoadmapPhaseState
  later : RoadmapPhaseState

record ProductionGoldenSplit : Set where
  constructor productionGoldenSplit
  field
    productionRepositoryReference : String
    goldenRepositoryReference : String
    productionMayWeakenGoldenFirewall : Bool
    productionMayConservativelyRefineGolden : Bool
    goldenReferenceIsRuntimeReceipt : Bool
    runtimeReceiptRequiredForSprintClosure : Bool

open ProductionGoldenSplit public

canonicalProductionGoldenSplit : ProductionGoldenSplit
canonicalProductionGoldenSplit =
  productionGoldenSplit
    "chboishabba/slr"
    "chboishabba/dashi_agda"
    false
    true
    false
    true

record CapabilitySprint : Set where
  constructor capabilitySprint
  field
    sprintReference : String
    state : RoadmapPhaseState
    capabilityReference : String
    exitGateReference : String

open CapabilitySprint public

productionRoadmap : List CapabilitySprint
productionRoadmap =
    capabilitySprint
      "1"
      active
      "recurrent acquisition machine: residual -> producer plan -> bounded physical acquisition -> candidate evidence -> review/payment -> fresh world -> re-diagnosis"
      "M1.1-M1.5 implemented; exact Rust runtime receipt, persisted campaign replay and exact Agda kernel receipt required before closure"
  ∷ capabilitySprint
      "2"
      next
      "canonical evidence convergence across world, legal-authority and narrative acquisition"
      "one manifestation/source-revision/span/observation substrate replays exact provenance across producer families"
  ∷ capabilitySprint
      "3"
      next
      "reviewed world state to typed legal issue projection"
      "one matter maps reviewed evidence and pinned authority into support/contradiction/unknown element state without semantic overpromotion"
  ∷ capabilitySprint
      "4"
      later
      "legal reasoning kernel plus human-facing matter/source/issue/evidence/receipt product surface"
      "complete issue reasoning remains inspectable through why/what-missing/as-at queries and the UI introduces no parallel ontology"
  ∷ []

record SprintDiscipline : Set where
  constructor sprintDiscipline
  field
    oneFileChangeIsSprintByDefault : Bool
    oneAdapterChangeIsSprintByDefault : Bool
    compileOnlyTrancheClosesSprint : Bool
    unitOnlyTrancheClosesSprint : Bool
    endToEndCapabilityGateRequired : Bool
    persistedReplayableReceiptRequired : Bool
    goldenParityRequired : Bool
    workByMinCut : Bool
    parallelIndependentOwners : Bool
    reopenPaidArchitectureWithoutCounterexample : Bool
    addProviderWithoutLiveResidualDemand : Bool

open SprintDiscipline public

canonicalSprintDiscipline : SprintDiscipline
canonicalSprintDiscipline =
  sprintDiscipline
    false
    false
    false
    false
    true
    true
    true
    true
    true
    false
    false

record WorldToLawProjectionBoundary : Set where
  constructor worldToLawProjectionBoundary
  field
    reviewedObservationMayProduceEventCandidate : Bool
    reviewedEventMaySupportClaimEvent : Bool
    reviewedEventMaySupplyElementEvidence : Bool
    legalSourceMaySupplyProvision : Bool
    provisionMaySupplyWrongElementRequirement : Bool
    eventExistenceCreatesWrong : Bool
    harmCreatesWrong : Bool
    wikidataClassCreatesLegalCategory : Bool
    sourcePresenceCreatesApplicability : Bool
    candidateElementMatchMeansSatisfiedElement : Bool
    unknownMayBeSilentlyCoercedFalse : Bool

open WorldToLawProjectionBoundary public

canonicalWorldToLawProjectionBoundary : WorldToLawProjectionBoundary
canonicalWorldToLawProjectionBoundary =
  worldToLawProjectionBoundary
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data MicroTrancheIsCompletedCapabilitySprint : Set where
data RuntimeMayWeakenGoldenSemanticFirewall : Set where
data EventExistenceCreatesLegalWrong : Set where
data OntologyClassificationCreatesLegalClassification : Set where
data UnknownMayCollapseToFalse : Set where

microTrancheIsNotCapabilitySprint :
  MicroTrancheIsCompletedCapabilitySprint → ⊥
microTrancheIsNotCapabilitySprint ()

runtimeCannotWeakenGoldenFirewall :
  RuntimeMayWeakenGoldenSemanticFirewall → ⊥
runtimeCannotWeakenGoldenFirewall ()

eventDoesNotCreateWrong :
  EventExistenceCreatesLegalWrong → ⊥
eventDoesNotCreateWrong ()

ontologyClassDoesNotCreateLegalClass :
  OntologyClassificationCreatesLegalClassification → ⊥
ontologyClassDoesNotCreateLegalClass ()

unknownDoesNotCollapseToFalse :
  UnknownMayCollapseToFalse → ⊥
unknownDoesNotCollapseToFalse ()

consumerAnchor : Consumer.ConsumerRequirementV2Parity
consumerAnchor = Consumer.canonicalConsumerRequirementV2Parity

plannerAnchor : Planner.ResidualDrivenProducerPlannerParity
plannerAnchor = Planner.canonicalResidualDrivenProducerPlannerParity

reviewAnchor : Review.ReviewedEvidencePaymentParity
reviewAnchor = Review.canonicalReviewedEvidencePaymentParity

iterationAnchor : Iteration.IterationControlParity
iterationAnchor = Iteration.canonicalIterationControlParity

suiteAnchor : Suite.SuiteConvergenceLaw
suiteAnchor = Suite.canonicalSuiteConvergenceLaw

physicalTransportAnchor : Physical.PhysicalObjectAcquisitionPolicy
physicalTransportAnchor = Physical.canonicalPhysicalObjectAcquisitionPolicy

externalOntologyAnchor : External.ExternalOntologyPolicy
externalOntologyAnchor = External.canonicalExternalOntologyPolicy


sprint1Anchor : Sprint1.Sprint1ExitGate
sprint1Anchor = Sprint1.currentSprint1ExitGate
