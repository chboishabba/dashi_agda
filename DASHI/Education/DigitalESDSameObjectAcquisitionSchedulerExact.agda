module DASHI.Education.DigitalESDSameObjectAcquisitionSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Acquisition
import DASHI.Education.DigitalESDICTLifecycleCircularitySnowballExact as ICT

------------------------------------------------------------------------
-- SAME-OBJECT ACQUISITION SCHEDULER
--
-- This is a producer router over already-declared acquisition debt.  It does
-- not create evidence and it does not permit literature similarity, standards,
-- or citations to discharge same-object, future, context-transfer, or
-- participant-authority obligations.
--
-- Standing attribution invariant:
--   * source identity + role + same-object status survive every round;
--   * citation imports neither proof nor authority;
--   * DASHI scheduling is DASHI synthesis, not a theorem of cited sources;
--   * acquisition may occur out of dependency order;
--   * downstream payment cannot skip an unpaid dependency.
------------------------------------------------------------------------

data ResidualProducer : Set where
  sourceRoleReceiptProducer : ResidualProducer
  contextEvidenceProducer : ResidualProducer
  interventionLCIProducer : ResidualProducer
  deploymentReferenceSystemProducer : ResidualProducer
  hardwareCircularityProducer : ResidualProducer
  procurementRepairSupportProducer : ResidualProducer
  serviceLifeSupportProducer : ResidualProducer
  interoperabilityPersistenceProducer : ResidualProducer
  longitudinalFollowupProducer : ResidualProducer
  contextGeneralisationReceiptProducer : ResidualProducer
  participantAuthorityReceiptProducer : ResidualProducer

producerLabel : ResidualProducer → String
producerLabel sourceRoleReceiptProducer = "source-role attribution receipt"
producerLabel contextEvidenceProducer = "bounded contextual evidence producer"
producerLabel interventionLCIProducer = "same-object intervention life-cycle inventory producer"
producerLabel deploymentReferenceSystemProducer = "consumer-declared same-object reference-system producer"
producerLabel hardwareCircularityProducer = "selected-hardware circularity observation producer"
producerLabel procurementRepairSupportProducer = "procurement / spare-parts / documentation / repair-support producer"
producerLabel serviceLifeSupportProducer = "service-life / software-update / support-window producer"
producerLabel interoperabilityPersistenceProducer = "persistent export / interface / migration-path observation producer"
producerLabel longitudinalFollowupProducer = "future same-cohort/intervention longitudinal follow-up producer"
producerLabel contextGeneralisationReceiptProducer = "canonical context-generalisation receipt producer"
producerLabel participantAuthorityReceiptProducer = "participant epistemic-authority / governance receipt producer"

------------------------------------------------------------------------
-- Parent acquisition leaves.
--
-- Paid contextual leaves retain source-role/context producers for provenance;
-- unpaid leaves route to the producer that can actually change their payment
-- status.  The richer `requiredProducersForAcquisitionLeaf` records conjunctions
-- where one producer is insufficient.
------------------------------------------------------------------------

producerForAcquisitionLeaf :
  Acquisition.AcquisitionLeaf → ResidualProducer
producerForAcquisitionLeaf Acquisition.exactCallAntecedentIdentity =
  sourceRoleReceiptProducer
producerForAcquisitionLeaf Acquisition.pedagogicalNonSufficiencyContext =
  contextEvidenceProducer
producerForAcquisitionLeaf Acquisition.genericInfrastructureExternalityContext =
  contextEvidenceProducer
producerForAcquisitionLeaf Acquisition.educationSpecificLifecycleMeasurement =
  interventionLCIProducer
producerForAcquisitionLeaf Acquisition.longitudinalInterventionImpact =
  longitudinalFollowupProducer
producerForAcquisitionLeaf Acquisition.esdParticipantGovernanceTransfer =
  participantAuthorityReceiptProducer
producerForAcquisitionLeaf Acquisition.openInteroperabilityDurability =
  interoperabilityPersistenceProducer

requiredProducersForAcquisitionLeaf :
  Acquisition.AcquisitionLeaf → List ResidualProducer
requiredProducersForAcquisitionLeaf Acquisition.exactCallAntecedentIdentity =
  sourceRoleReceiptProducer ∷ []
requiredProducersForAcquisitionLeaf Acquisition.pedagogicalNonSufficiencyContext =
  contextEvidenceProducer ∷ []
requiredProducersForAcquisitionLeaf Acquisition.genericInfrastructureExternalityContext =
  contextEvidenceProducer ∷ []
requiredProducersForAcquisitionLeaf Acquisition.educationSpecificLifecycleMeasurement =
  interventionLCIProducer
  ∷ deploymentReferenceSystemProducer
  ∷ []
requiredProducersForAcquisitionLeaf Acquisition.longitudinalInterventionImpact =
  longitudinalFollowupProducer ∷ []
requiredProducersForAcquisitionLeaf Acquisition.esdParticipantGovernanceTransfer =
  contextGeneralisationReceiptProducer
  ∷ participantAuthorityReceiptProducer
  ∷ []
requiredProducersForAcquisitionLeaf Acquisition.openInteroperabilityDurability =
  hardwareCircularityProducer
  ∷ procurementRepairSupportProducer
  ∷ serviceLifeSupportProducer
  ∷ interoperabilityPersistenceProducer
  ∷ []

------------------------------------------------------------------------
-- Refined ICT lifecycle/circularity leaves.
------------------------------------------------------------------------

producerForRefinedLifecycle : ICT.RefinedLifecycleLeaf → ResidualProducer
producerForRefinedLifecycle ICT.ictLifecycleMethod = sourceRoleReceiptProducer
producerForRefinedLifecycle ICT.ictCircularityMethod = sourceRoleReceiptProducer
producerForRefinedLifecycle ICT.deploymentSpecificLCI = interventionLCIProducer
producerForRefinedLifecycle ICT.deploymentReferenceSystem = deploymentReferenceSystemProducer
producerForRefinedLifecycle ICT.deploymentHardwareCircularity = hardwareCircularityProducer
producerForRefinedLifecycle ICT.deploymentRepairSupport = procurementRepairSupportProducer
producerForRefinedLifecycle ICT.deploymentServiceLife = serviceLifeSupportProducer
producerForRefinedLifecycle ICT.deploymentInteroperabilityPersistence = interoperabilityPersistenceProducer

------------------------------------------------------------------------
-- Citation-resistant dependency firewalls.
------------------------------------------------------------------------

data ExternalCitationPaysSameObjectLCI : Set where

externalCitationDoesNotPaySameObjectLCI :
  ExternalCitationPaysSameObjectLCI → ⊥
externalCitationDoesNotPaySameObjectLCI ()

data PriorStudyPaysFutureLongitudinalOutcome : Set where

priorStudyDoesNotPayFutureLongitudinalOutcome :
  PriorStudyPaysFutureLongitudinalOutcome → ⊥
priorStudyDoesNotPayFutureLongitudinalOutcome ()

data LiteratureSimilarityCreatesContextTransferReceipt : Set where

literatureSimilarityDoesNotCreateContextTransferReceipt :
  LiteratureSimilarityCreatesContextTransferReceipt → ⊥
literatureSimilarityDoesNotCreateContextTransferReceipt ()

data StandardsDocumentProvesActualRepairSupport : Set where

standardsDocumentDoesNotProveActualRepairSupport :
  StandardsDocumentProvesActualRepairSupport → ⊥
standardsDocumentDoesNotProveActualRepairSupport ()

data OpenStandardsDocumentProvesPersistentInteroperability : Set where

openStandardsDocumentDoesNotProvePersistentInteroperability :
  OpenStandardsDocumentProvesPersistentInteroperability → ⊥
openStandardsDocumentDoesNotProvePersistentInteroperability ()

data CitationCreatesParticipantAuthority : Set where

citationDoesNotCreateParticipantAuthority :
  CitationCreatesParticipantAuthority → ⊥
citationDoesNotCreateParticipantAuthority ()

data AcquisitionOrderCreatesPaymentOrder : Set where

acquisitionOrderDoesNotCreatePaymentOrder :
  AcquisitionOrderCreatesPaymentOrder → ⊥
acquisitionOrderDoesNotCreatePaymentOrder ()

data PaidSiblingAllowsSkippedDependency : Set where

paidSiblingDoesNotAllowSkippedDependency :
  PaidSiblingAllowsSkippedDependency → ⊥
paidSiblingDoesNotAllowSkippedDependency ()

------------------------------------------------------------------------
-- Current producer frontier.  This is a work queue, not evidence and not an
-- empirical conclusion.  Duplicate producers are intentionally collapsed here
-- only at the scheduling layer; each acquired receipt must still retain its
-- own same-object/source provenance at payment time.
------------------------------------------------------------------------

currentProducerFrontier : List ResidualProducer
currentProducerFrontier =
  interventionLCIProducer
  ∷ deploymentReferenceSystemProducer
  ∷ hardwareCircularityProducer
  ∷ procurementRepairSupportProducer
  ∷ serviceLifeSupportProducer
  ∷ interoperabilityPersistenceProducer
  ∷ longitudinalFollowupProducer
  ∷ contextGeneralisationReceiptProducer
  ∷ participantAuthorityReceiptProducer
  ∷ []

record SameObjectAcquisitionSchedulerBoundary : Set where
  constructor same-object-acquisition-scheduler-boundary
  field
    schedulerCreatesEvidence : Bool
    schedulerCreatesEvidenceIsFalse : schedulerCreatesEvidence ≡ false

    externalCitationPaysSameObjectObservation : Bool
    externalCitationPaysSameObjectObservationIsFalse :
      externalCitationPaysSameObjectObservation ≡ false

    priorStudyPaysFutureObservation : Bool
    priorStudyPaysFutureObservationIsFalse :
      priorStudyPaysFutureObservation ≡ false

    sourceIdentityRoleAndSameObjectRetained : Bool
    sourceIdentityRoleAndSameObjectRetainedIsTrue :
      sourceIdentityRoleAndSameObjectRetained ≡ true

    citationImportsProof : Bool
    citationImportsProofIsFalse : citationImportsProof ≡ false

    citationCreatesAuthority : Bool
    citationCreatesAuthorityIsFalse : citationCreatesAuthority ≡ false

    acquisitionMayOccurOutOfDependencyOrder : Bool
    acquisitionMayOccurOutOfDependencyOrderIsTrue :
      acquisitionMayOccurOutOfDependencyOrder ≡ true

    downstreamPaymentMaySkipUnpaidDependency : Bool
    downstreamPaymentMaySkipUnpaidDependencyIsFalse :
      downstreamPaymentMaySkipUnpaidDependency ≡ false

    dashiSchedulerIsSourceTheorem : Bool
    dashiSchedulerIsSourceTheoremIsFalse : dashiSchedulerIsSourceTheorem ≡ false

open SameObjectAcquisitionSchedulerBoundary public

canonicalSameObjectAcquisitionSchedulerBoundary :
  SameObjectAcquisitionSchedulerBoundary
canonicalSameObjectAcquisitionSchedulerBoundary =
  same-object-acquisition-scheduler-boundary
    false refl
    false refl
    false refl
    true refl
    false refl
    false refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- BIDI scheduling receipt: an unpaid coordinate determines a producer request;
-- a producer's eventual output may return only as a provenance-bearing receipt
-- for that coordinate.  The schedule itself never promotes payment.
------------------------------------------------------------------------

record ProducerScheduleReceipt : Set where
  constructor producer-schedule-receipt
  field
    residualLabel : String
    requestedProducer : ResidualProducer
    requestReason : String
    sameObjectRequired : Bool
    sourceRoleRetained : Bool
    outputAutomaticallyPaysResidual : Bool

open ProducerScheduleReceipt public

lifecycleInventorySchedule : ProducerScheduleReceipt
lifecycleInventorySchedule =
  producer-schedule-receipt
    "education-specific lifecycle measurement"
    interventionLCIProducer
    "method sources are paid; the proposed intervention's actual inventory is not"
    true true false

longitudinalImpactSchedule : ProducerScheduleReceipt
longitudinalImpactSchedule =
  producer-schedule-receipt
    "longitudinal intervention impact"
    longitudinalFollowupProducer
    "prior longitudinal ESD studies bound plausibility/method, but cannot observe this intervention's future outcome"
    true true false

participantGovernanceSchedule : ProducerScheduleReceipt
participantGovernanceSchedule =
  producer-schedule-receipt
    "ESD participant governance transfer"
    participantAuthorityReceiptProducer
    "procedural ethics and prior participatory studies do not create participant epistemic authority in this context"
    true true false

interoperabilityPersistenceSchedule : ProducerScheduleReceipt
interoperabilityPersistenceSchedule =
  producer-schedule-receipt
    "open interoperability / durability"
    interoperabilityPersistenceProducer
    "standards and charters define relevant coordinates but cannot observe persistence of the selected deployment through time"
    true true false

highestAlphaSchedulerReading : String
highestAlphaSchedulerReading =
  "The Pareto frontier is now partitioned by evidence producer rather than citation count. Method/context sources may be acquired and paid out of order, but same-object deployment, future longitudinal, context-transfer and participant-authority coordinates remain blocked until their own provenance-bearing producers return receipts; no paid sibling or citation can skip those dependencies."
