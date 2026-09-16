module DASHI.Education.DigitalESDSameObjectAcquisitionSchedulerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.RequirementProducerSchedulerExact as CoreScheduler
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Acquisition
import DASHI.Education.DigitalESDICTLifecycleCircularitySnowballExact as ICT
import DASHI.Education.DigitalESDPaperTypeRequirementParetoExact as Paper

------------------------------------------------------------------------
-- SAME-OBJECT ACQUISITION SCHEDULER ADAPTER
--
-- Local content: digital-ESD questions, coordinates and producer identities.
-- Scheduling semantics come from RequirementProducerSchedulerExact; Pareto/MDL
-- eligibility semantics come from AdmissibleConsumerMDLHyperfabricExact.
-- Paper-type scope comes from DigitalESDPaperTypeRequirementParetoExact.
--
-- Standing attribution invariant:
--   source identity + role + same-object status survive every round;
--   citation imports neither proof nor authority;
--   DASHI scheduling is DASHI synthesis, not a theorem of cited sources;
--   acquisition may occur out of dependency order;
--   downstream payment cannot skip an unpaid dependency.
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

producerForAcquisitionLeaf : Acquisition.AcquisitionLeaf → ResidualProducer
producerForAcquisitionLeaf Acquisition.exactCallAntecedentIdentity = sourceRoleReceiptProducer
producerForAcquisitionLeaf Acquisition.pedagogicalNonSufficiencyContext = contextEvidenceProducer
producerForAcquisitionLeaf Acquisition.genericInfrastructureExternalityContext = contextEvidenceProducer
producerForAcquisitionLeaf Acquisition.educationSpecificLifecycleMeasurement = interventionLCIProducer
producerForAcquisitionLeaf Acquisition.longitudinalInterventionImpact = longitudinalFollowupProducer
producerForAcquisitionLeaf Acquisition.esdParticipantGovernanceTransfer = participantAuthorityReceiptProducer
producerForAcquisitionLeaf Acquisition.openInteroperabilityDurability = interoperabilityPersistenceProducer

requiredProducersForAcquisitionLeaf : Acquisition.AcquisitionLeaf → List ResidualProducer
requiredProducersForAcquisitionLeaf Acquisition.exactCallAntecedentIdentity = sourceRoleReceiptProducer ∷ []
requiredProducersForAcquisitionLeaf Acquisition.pedagogicalNonSufficiencyContext = contextEvidenceProducer ∷ []
requiredProducersForAcquisitionLeaf Acquisition.genericInfrastructureExternalityContext = contextEvidenceProducer ∷ []
requiredProducersForAcquisitionLeaf Acquisition.educationSpecificLifecycleMeasurement =
  interventionLCIProducer ∷ deploymentReferenceSystemProducer ∷ []
requiredProducersForAcquisitionLeaf Acquisition.longitudinalInterventionImpact =
  longitudinalFollowupProducer ∷ []
requiredProducersForAcquisitionLeaf Acquisition.esdParticipantGovernanceTransfer =
  contextGeneralisationReceiptProducer ∷ participantAuthorityReceiptProducer ∷ []
requiredProducersForAcquisitionLeaf Acquisition.openInteroperabilityDurability =
  hardwareCircularityProducer
  ∷ procurementRepairSupportProducer
  ∷ serviceLifeSupportProducer
  ∷ interoperabilityPersistenceProducer
  ∷ []

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
-- Consumer-/claim-relative application of the canonical scheduler.
--
-- Current conceptual-review work has literature/search/synthesis debt in the
-- paper-type scheduler, but no same-object empirical deployment obligation.
-- Those obligations reopen only when the manuscript makes the corresponding
-- empirical, durability, longitudinal, or participant-authority claim.
------------------------------------------------------------------------

data DigitalESDAcquisitionQuestion : Set where
  currentConceptualReviewSynthesis : DigitalESDAcquisitionQuestion
  empiricalInterventionLifecycleClaim : DigitalESDAcquisitionQuestion
  deploymentDurabilityClaim : DigitalESDAcquisitionQuestion
  longitudinalImpactClaim : DigitalESDAcquisitionQuestion
  participantGovernanceTransferClaim : DigitalESDAcquisitionQuestion

data SameObjectCoordinate : Set where
  sameObjectInterventionLCI : SameObjectCoordinate
  sameObjectReferenceSystem : SameObjectCoordinate
  sameObjectHardwareCircularity : SameObjectCoordinate
  sameObjectRepairSupport : SameObjectCoordinate
  sameObjectServiceLife : SameObjectCoordinate
  sameObjectInteroperabilityPersistence : SameObjectCoordinate
  sameObjectLongitudinalImpact : SameObjectCoordinate
  contextGeneralisationAdmission : SameObjectCoordinate
  participantEpistemicAuthority : SameObjectCoordinate

requiredForDigitalESD : DigitalESDAcquisitionQuestion → SameObjectCoordinate → Bool
requiredForDigitalESD currentConceptualReviewSynthesis _ = false
requiredForDigitalESD empiricalInterventionLifecycleClaim sameObjectInterventionLCI = true
requiredForDigitalESD empiricalInterventionLifecycleClaim sameObjectReferenceSystem = true
requiredForDigitalESD empiricalInterventionLifecycleClaim _ = false
requiredForDigitalESD deploymentDurabilityClaim sameObjectHardwareCircularity = true
requiredForDigitalESD deploymentDurabilityClaim sameObjectRepairSupport = true
requiredForDigitalESD deploymentDurabilityClaim sameObjectServiceLife = true
requiredForDigitalESD deploymentDurabilityClaim sameObjectInteroperabilityPersistence = true
requiredForDigitalESD deploymentDurabilityClaim _ = false
requiredForDigitalESD longitudinalImpactClaim sameObjectLongitudinalImpact = true
requiredForDigitalESD longitudinalImpactClaim _ = false
requiredForDigitalESD participantGovernanceTransferClaim contextGeneralisationAdmission = true
requiredForDigitalESD participantGovernanceTransferClaim participantEpistemicAuthority = true
requiredForDigitalESD participantGovernanceTransferClaim _ = false

closedDigitalESD : SameObjectCoordinate → Bool
closedDigitalESD _ = false

producerForCoordinate : SameObjectCoordinate → ResidualProducer
producerForCoordinate sameObjectInterventionLCI = interventionLCIProducer
producerForCoordinate sameObjectReferenceSystem = deploymentReferenceSystemProducer
producerForCoordinate sameObjectHardwareCircularity = hardwareCircularityProducer
producerForCoordinate sameObjectRepairSupport = procurementRepairSupportProducer
producerForCoordinate sameObjectServiceLife = serviceLifeSupportProducer
producerForCoordinate sameObjectInteroperabilityPersistence = interoperabilityPersistenceProducer
producerForCoordinate sameObjectLongitudinalImpact = longitudinalFollowupProducer
producerForCoordinate contextGeneralisationAdmission = contextGeneralisationReceiptProducer
producerForCoordinate participantEpistemicAuthority = participantAuthorityReceiptProducer

digitalESDAcquisitionRequirementSystem : CoreScheduler.RequirementSystem
digitalESDAcquisitionRequirementSystem =
  CoreScheduler.requirement-system
    DigitalESDAcquisitionQuestion
    SameObjectCoordinate
    ResidualProducer
    requiredForDigitalESD
    closedDigitalESD
    producerForCoordinate
    "claim-relative digital-ESD same-object/future/context/authority requirements"
    "same-object measurement, longitudinal observation, canonical context-generalisation and participant-authority receipt producers"

currentPaperTypeRetained : Paper.PaperType
currentPaperTypeRetained = Paper.currentPaperType

currentPaperTypeIsConceptualReview :
  currentPaperTypeRetained ≡ Paper.integrativeConceptualReview
currentPaperTypeIsConceptualReview = refl

lifecycleInventoryMissing :
  CoreScheduler.MissingFor
    digitalESDAcquisitionRequirementSystem
    empiricalInterventionLifecycleClaim
    sameObjectInterventionLCI
lifecycleInventoryMissing = refl , refl

lifecycleInventoryMissingReceipt :
  CoreScheduler.MissingCoordinateReceipt
    digitalESDAcquisitionRequirementSystem
    empiricalInterventionLifecycleClaim
lifecycleInventoryMissingReceipt =
  CoreScheduler.missing-coordinate-receipt sameObjectInterventionLCI lifecycleInventoryMissing

lifecycleInventoryScheduledProducer : ResidualProducer
lifecycleInventoryScheduledProducer = CoreScheduler.scheduledProducer lifecycleInventoryMissingReceipt

lifecycleInventoryScheduledProducerIsCanonical :
  lifecycleInventoryScheduledProducer ≡ interventionLCIProducer
lifecycleInventoryScheduledProducerIsCanonical = refl

canonicalSchedulerBoundaryRetained : CoreScheduler.RequirementProducerSchedulerBoundary
canonicalSchedulerBoundaryRetained = CoreScheduler.canonicalRequirementProducerSchedulerBoundary

producerIdentityStillDoesNotCloseRequirement :
  CoreScheduler.ProducerExistenceImpliesCoordinateClosedPermission → ⊥
producerIdentityStillDoesNotCloseRequirement = CoreScheduler.producerExistenceDoesNotAutoCloseCoordinate

canonicalProducerParetoEligibilityBoundary : MDL.AdmissibleConsumerMDLBoundary
canonicalProducerParetoEligibilityBoundary = MDL.canonicalAdmissibleConsumerMDLBoundary

------------------------------------------------------------------------
-- Citation-resistant dependency firewalls.
------------------------------------------------------------------------

data ExternalCitationPaysSameObjectLCI : Set where
externalCitationDoesNotPaySameObjectLCI : ExternalCitationPaysSameObjectLCI → ⊥
externalCitationDoesNotPaySameObjectLCI ()

data PriorStudyPaysFutureLongitudinalOutcome : Set where
priorStudyDoesNotPayFutureLongitudinalOutcome : PriorStudyPaysFutureLongitudinalOutcome → ⊥
priorStudyDoesNotPayFutureLongitudinalOutcome ()

data LiteratureSimilarityCreatesContextTransferReceipt : Set where
literatureSimilarityDoesNotCreateContextTransferReceipt : LiteratureSimilarityCreatesContextTransferReceipt → ⊥
literatureSimilarityDoesNotCreateContextTransferReceipt ()

data StandardsDocumentProvesActualRepairSupport : Set where
standardsDocumentDoesNotProveActualRepairSupport : StandardsDocumentProvesActualRepairSupport → ⊥
standardsDocumentDoesNotProveActualRepairSupport ()

data OpenStandardsDocumentProvesPersistentInteroperability : Set where
openStandardsDocumentDoesNotProvePersistentInteroperability : OpenStandardsDocumentProvesPersistentInteroperability → ⊥
openStandardsDocumentDoesNotProvePersistentInteroperability ()

data CitationCreatesParticipantAuthority : Set where
citationDoesNotCreateParticipantAuthority : CitationCreatesParticipantAuthority → ⊥
citationDoesNotCreateParticipantAuthority ()

data AcquisitionOrderCreatesPaymentOrder : Set where
acquisitionOrderDoesNotCreatePaymentOrder : AcquisitionOrderCreatesPaymentOrder → ⊥
acquisitionOrderDoesNotCreatePaymentOrder ()

data PaidSiblingAllowsSkippedDependency : Set where
paidSiblingDoesNotAllowSkippedDependency : PaidSiblingAllowsSkippedDependency → ⊥
paidSiblingDoesNotAllowSkippedDependency ()

------------------------------------------------------------------------
-- Potential future same-object producer frontier.  It is not the current
-- conceptual-review work queue.  Current manuscript work is governed by the
-- paper-type owner; these producers activate only under the claims above.
------------------------------------------------------------------------

potentialSameObjectProducerFrontier : List ResidualProducer
potentialSameObjectProducerFrontier =
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

currentProducerFrontier : List ResidualProducer
currentProducerFrontier = []

record SameObjectAcquisitionSchedulerBoundary : Set where
  constructor same-object-acquisition-scheduler-boundary
  field
    schedulerCreatesEvidence : Bool
    schedulerCreatesEvidenceIsFalse : schedulerCreatesEvidence ≡ false
    externalCitationPaysSameObjectObservation : Bool
    externalCitationPaysSameObjectObservationIsFalse : externalCitationPaysSameObjectObservation ≡ false
    priorStudyPaysFutureObservation : Bool
    priorStudyPaysFutureObservationIsFalse : priorStudyPaysFutureObservation ≡ false
    sourceIdentityRoleAndSameObjectRetained : Bool
    sourceIdentityRoleAndSameObjectRetainedIsTrue : sourceIdentityRoleAndSameObjectRetained ≡ true
    citationImportsProof : Bool
    citationImportsProofIsFalse : citationImportsProof ≡ false
    citationCreatesAuthority : Bool
    citationCreatesAuthorityIsFalse : citationCreatesAuthority ≡ false
    acquisitionMayOccurOutOfDependencyOrder : Bool
    acquisitionMayOccurOutOfDependencyOrderIsTrue : acquisitionMayOccurOutOfDependencyOrder ≡ true
    downstreamPaymentMaySkipUnpaidDependency : Bool
    downstreamPaymentMaySkipUnpaidDependencyIsFalse : downstreamPaymentMaySkipUnpaidDependency ≡ false
    dashiSchedulerIsSourceTheorem : Bool
    dashiSchedulerIsSourceTheoremIsFalse : dashiSchedulerIsSourceTheorem ≡ false
    canonicalRequirementSchedulerReused : Bool
    canonicalRequirementSchedulerReusedIsTrue : canonicalRequirementSchedulerReused ≡ true
    paretoRankingRequiresEligibilityFirst : Bool
    paretoRankingRequiresEligibilityFirstIsTrue : paretoRankingRequiresEligibilityFirst ≡ true
    sameObjectDebtAutomaticallyBecomesCurrentPaperRequirement : Bool
    sameObjectDebtAutomaticallyBecomesCurrentPaperRequirementIsFalse :
      sameObjectDebtAutomaticallyBecomesCurrentPaperRequirement ≡ false

open SameObjectAcquisitionSchedulerBoundary public

canonicalSameObjectAcquisitionSchedulerBoundary : SameObjectAcquisitionSchedulerBoundary
canonicalSameObjectAcquisitionSchedulerBoundary =
  same-object-acquisition-scheduler-boundary
    false refl false refl false refl true refl false refl false refl true refl
    false refl false refl true refl true refl false refl

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
    "empirical intervention lifecycle claim"
    interventionLCIProducer
    "method sources are paid; an empirical claim about the proposed intervention still needs its actual inventory"
    true true false

longitudinalImpactSchedule : ProducerScheduleReceipt
longitudinalImpactSchedule =
  producer-schedule-receipt
    "same-object longitudinal impact claim"
    longitudinalFollowupProducer
    "prior longitudinal ESD studies constrain method/context but cannot observe this intervention's future outcome"
    true true false

participantGovernanceSchedule : ProducerScheduleReceipt
participantGovernanceSchedule =
  producer-schedule-receipt
    "participant governance transfer claim"
    participantAuthorityReceiptProducer
    "procedural ethics and prior participatory studies do not create participant epistemic authority in this context"
    true true false

interoperabilityPersistenceSchedule : ProducerScheduleReceipt
interoperabilityPersistenceSchedule =
  producer-schedule-receipt
    "deployment durability/interoperability claim"
    interoperabilityPersistenceProducer
    "standards and charters define relevant coordinates but cannot observe persistence of the selected deployment through time"
    true true false

highestAlphaSchedulerReading : String
highestAlphaSchedulerReading =
  "Same-object/future/authority debt remains explicit but is claim-relative. The current integrative conceptual review does not inherit empirical-intervention LCI, durability, longitudinal-observation or participant-authority obligations merely because those residuals exist. If a later manuscript promotes the corresponding empirical/deployment/governance claim, the canonical requirement scheduler reopens the exact producer; Pareto ranking remains eligibility-gated and citations cannot skip the unpaid dependency."
