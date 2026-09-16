module DASHI.Education.DigitalESDParticipantGovernanceContextTransferRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Education.DigitalESDParticipantGovernanceContextTransferExact as Transfer
import DASHI.Education.DigitalESDSameObjectAcquisitionSchedulerExact as Scheduler

conceptualReviewDoesNotRequireAuthorityRegression :
  Scheduler.requiredForDigitalESD
    Scheduler.currentConceptualReviewSynthesis
    Scheduler.participantEpistemicAuthority
  ≡ false
conceptualReviewDoesNotRequireAuthorityRegression = refl

participantTransferRequiresContextRegression :
  Scheduler.requiredForDigitalESD
    Scheduler.participantGovernanceTransferClaim
    Scheduler.contextGeneralisationAdmission
  ≡ true
participantTransferRequiresContextRegression = refl

participantTransferRequiresAuthorityRegression :
  Scheduler.requiredForDigitalESD
    Scheduler.participantGovernanceTransferClaim
    Scheduler.participantEpistemicAuthority
  ≡ true
participantTransferRequiresAuthorityRegression = refl

admissionRequiresBothReceiptsRegression :
  (context : Learning.ContextGeneralisationReceipt) →
  (authority : Transfer.ParticipantAuthorityReceipt) →
  Transfer.ParticipantGovernanceContextTransferAdmission
admissionRequiresBothReceiptsRegression = Transfer.admitParticipantGovernanceContextTransfer

literatureCannotCreateAuthorityRegression :
  Transfer.LiteratureCreatesParticipantAuthority → ⊥
literatureCannotCreateAuthorityRegression =
  Transfer.literatureDoesNotCreateParticipantAuthority

consentCannotCreateAuthorityRegression :
  Transfer.ConsentCreatesParticipantAuthority → ⊥
consentCannotCreateAuthorityRegression =
  Transfer.consentDoesNotCreateParticipantAuthority

proceduralEthicsCannotCreateAuthorityRegression :
  Transfer.ProceduralEthicsCreatesParticipantAuthority → ⊥
proceduralEthicsCannotCreateAuthorityRegression =
  Transfer.proceduralEthicsDoesNotCreateParticipantAuthority

aliceCorpusCannotCreateLocalAuthorityRegression :
  Transfer.AliceCorpusCreatesLocalParticipantAuthority → ⊥
aliceCorpusCannotCreateLocalAuthorityRegression =
  Transfer.aliceCorpusDoesNotCreateLocalParticipantAuthority

contextGeneralisationRemainsNonAutomaticRegression :
  (context : Learning.ContextGeneralisationReceipt) →
  Learning.generalisationIsAutomatic context ≡ false
contextGeneralisationRemainsNonAutomaticRegression =
  Learning.generalisationIsAutomaticIsFalse

transferBoundaryRetainsAttributionRegression :
  Transfer.ParticipantGovernanceContextTransferBoundary.sourceRoleAndSameObjectRetained
    Transfer.canonicalParticipantGovernanceContextTransferBoundary
  ≡ true
transferBoundaryRetainsAttributionRegression = refl

transferBoundaryForbidsSkippedDependencyRegression :
  Transfer.ParticipantGovernanceContextTransferBoundary.downstreamPaymentMaySkipUnpaidDependency
    Transfer.canonicalParticipantGovernanceContextTransferBoundary
  ≡ false
transferBoundaryForbidsSkippedDependencyRegression = refl

transferBoundaryLabelsDASHISynthesisRegression :
  Transfer.ParticipantGovernanceContextTransferBoundary.transferRuleIsAliceEmpiricalFinding
    Transfer.canonicalParticipantGovernanceContextTransferBoundary
  ≡ false
transferBoundaryLabelsDASHISynthesisRegression = refl
