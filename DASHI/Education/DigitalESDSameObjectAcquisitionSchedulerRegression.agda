module DASHI.Education.DigitalESDSameObjectAcquisitionSchedulerRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Data.Empty using (⊥)

import DASHI.Core.RequirementProducerSchedulerExact as CoreScheduler
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Acquisition
import DASHI.Education.DigitalESDICTLifecycleCircularitySnowballExact as ICT
import DASHI.Education.DigitalESDPaperTypeRequirementParetoExact as Paper
import DASHI.Education.DigitalESDSameObjectAcquisitionSchedulerExact as Scheduler

lifecycleLeafProducerRegression :
  Scheduler.producerForRefinedLifecycle ICT.deploymentSpecificLCI
  ≡ Scheduler.interventionLCIProducer
lifecycleLeafProducerRegression = refl

referenceSystemProducerRegression :
  Scheduler.producerForRefinedLifecycle ICT.deploymentReferenceSystem
  ≡ Scheduler.deploymentReferenceSystemProducer
referenceSystemProducerRegression = refl

repairSupportProducerRegression :
  Scheduler.producerForRefinedLifecycle ICT.deploymentRepairSupport
  ≡ Scheduler.procurementRepairSupportProducer
repairSupportProducerRegression = refl

interoperabilityProducerRegression :
  Scheduler.producerForRefinedLifecycle ICT.deploymentInteroperabilityPersistence
  ≡ Scheduler.interoperabilityPersistenceProducer
interoperabilityProducerRegression = refl

longitudinalProducerRegression :
  Scheduler.producerForAcquisitionLeaf Acquisition.longitudinalInterventionImpact
  ≡ Scheduler.longitudinalFollowupProducer
longitudinalProducerRegression = refl

participantGovernanceProducerRegression :
  Scheduler.producerForAcquisitionLeaf Acquisition.esdParticipantGovernanceTransfer
  ≡ Scheduler.participantAuthorityReceiptProducer
participantGovernanceProducerRegression = refl

citationCannotPaySameObjectLCIRegression :
  Scheduler.ExternalCitationPaysSameObjectLCI → ⊥
citationCannotPaySameObjectLCIRegression =
  Scheduler.externalCitationDoesNotPaySameObjectLCI

priorStudyCannotPayFutureOutcomeRegression :
  Scheduler.PriorStudyPaysFutureLongitudinalOutcome → ⊥
priorStudyCannotPayFutureOutcomeRegression =
  Scheduler.priorStudyDoesNotPayFutureLongitudinalOutcome

similarityCannotCreateTransferRegression :
  Scheduler.LiteratureSimilarityCreatesContextTransferReceipt → ⊥
similarityCannotCreateTransferRegression =
  Scheduler.literatureSimilarityDoesNotCreateContextTransferReceipt

standardCannotProveRepairSupportRegression :
  Scheduler.StandardsDocumentProvesActualRepairSupport → ⊥
standardCannotProveRepairSupportRegression =
  Scheduler.standardsDocumentDoesNotProveActualRepairSupport

openStandardCannotProvePersistenceRegression :
  Scheduler.OpenStandardsDocumentProvesPersistentInteroperability → ⊥
openStandardCannotProvePersistenceRegression =
  Scheduler.openStandardsDocumentDoesNotProvePersistentInteroperability

citationCannotCreateParticipantAuthorityRegression :
  Scheduler.CitationCreatesParticipantAuthority → ⊥
citationCannotCreateParticipantAuthorityRegression =
  Scheduler.citationDoesNotCreateParticipantAuthority

schedulerRetainsAttributionRegression :
  Scheduler.SameObjectAcquisitionSchedulerBoundary.sourceIdentityRoleAndSameObjectRetained
    Scheduler.canonicalSameObjectAcquisitionSchedulerBoundary
  ≡ true
schedulerRetainsAttributionRegression = refl

schedulerForbidsSkippedDependencyRegression :
  Scheduler.SameObjectAcquisitionSchedulerBoundary.downstreamPaymentMaySkipUnpaidDependency
    Scheduler.canonicalSameObjectAcquisitionSchedulerBoundary
  ≡ false
schedulerForbidsSkippedDependencyRegression = refl

------------------------------------------------------------------------
-- The domain adapter reuses the canonical requirement scheduler and is
-- claim/consumer-relative.  Current conceptual-review synthesis does not
-- silently acquire empirical-intervention same-object obligations.
------------------------------------------------------------------------

canonicalSchedulerReuseRegression : CoreScheduler.RequirementSystem
canonicalSchedulerReuseRegression =
  Scheduler.digitalESDAcquisitionRequirementSystem

currentPaperTypeRegression : Paper.PaperType
currentPaperTypeRegression = Paper.currentPaperType

conceptualReviewLCINotRequiredRegression :
  Scheduler.requiredForDigitalESD
    Scheduler.currentConceptualReviewSynthesis
    Scheduler.sameObjectInterventionLCI
  ≡ false
conceptualReviewLCINotRequiredRegression = refl

empiricalLifecycleLCIRequiredRegression :
  Scheduler.requiredForDigitalESD
    Scheduler.empiricalInterventionLifecycleClaim
    Scheduler.sameObjectInterventionLCI
  ≡ true
empiricalLifecycleLCIRequiredRegression = refl

lifecycleInventoryMissingRegression :
  CoreScheduler.MissingFor
    Scheduler.digitalESDAcquisitionRequirementSystem
    Scheduler.empiricalInterventionLifecycleClaim
    Scheduler.sameObjectInterventionLCI
lifecycleInventoryMissingRegression = refl , refl

canonicalScheduledLCIProducerRegression :
  CoreScheduler.scheduledProducer Scheduler.lifecycleInventoryMissingReceipt
  ≡ Scheduler.interventionLCIProducer
canonicalScheduledLCIProducerRegression = refl

longitudinalClaimOnlyRequiresFollowupRegression :
  Scheduler.requiredForDigitalESD
    Scheduler.longitudinalImpactClaim
    Scheduler.sameObjectLongitudinalImpact
  ≡ true
longitudinalClaimOnlyRequiresFollowupRegression = refl

participantAuthorityClaimRequiresAuthorityRegression :
  Scheduler.requiredForDigitalESD
    Scheduler.participantGovernanceTransferClaim
    Scheduler.participantEpistemicAuthority
  ≡ true
participantAuthorityClaimRequiresAuthorityRegression = refl

canonicalSchedulerBoundaryRegression :
  CoreScheduler.RequirementProducerSchedulerBoundary.producerIdentityAloneClosesRequirement
    CoreScheduler.canonicalRequirementProducerSchedulerBoundary
  ≡ false
canonicalSchedulerBoundaryRegression = refl

------------------------------------------------------------------------
-- Pareto/MDL only begins after hard admissibility + consumer adequacy.
------------------------------------------------------------------------

canonicalParetoEligibilityBoundaryRegression : MDL.AdmissibleConsumerMDLBoundary
canonicalParetoEligibilityBoundaryRegression =
  Scheduler.canonicalProducerParetoEligibilityBoundary

inadmissibleCannotWinByShortCodeRegression :
  MDL.AdmissibleConsumerMDLBoundary.inadmissibleModelMayWinByShortCode
    Scheduler.canonicalProducerParetoEligibilityBoundary
  ≡ false
inadmissibleCannotWinByShortCodeRegression = refl

consumerInadequateCannotWinByShortCodeRegression :
  MDL.AdmissibleConsumerMDLBoundary.consumerInadequateModelMayWinByShortCode
    Scheduler.canonicalProducerParetoEligibilityBoundary
  ≡ false
consumerInadequateCannotWinByShortCodeRegression = refl

paretoAxesRemainApplicationDeclaredRegression :
  MDL.AdmissibleConsumerMDLBoundary.paretoAxesAreApplicationDeclared
    Scheduler.canonicalProducerParetoEligibilityBoundary
  ≡ true
paretoAxesRemainApplicationDeclaredRegression = refl
