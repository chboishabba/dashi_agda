module DASHI.Cognition.PNF.SensibLawBillyRemedyOperationalRealisationBidiExact where

------------------------------------------------------------------------
-- BILLY EFFECTIVE REMEDY / OPERATIONAL REALISATION BIDI
--
-- This owner consumes the existing Human Rights Committee / State-response
-- receipts and compiles them through the repository-wide operational-semantics
-- and Two-Eyed Seeing boundaries.
--
-- It does not create new Human Rights Committee holdings.  Realisation
-- contracts below are DASHI/SensibLaw implementation machinery.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK

------------------------------------------------------------------------
-- Means of implementation are typed by what they can actually do.
------------------------------------------------------------------------

data RemedyExecutionCapability : Set where
  canAuthorizePayment : RemedyExecutionCapability
  canAppropriateFunds : RemedyExecutionCapability
  canNegotiateCommunityAgreement : RemedyExecutionCapability
  canConstructOrMaintainProtectiveMeasures : RemedyExecutionCapability
  canMonitorOutcome : RemedyExecutionCapability
  canCorrectDeficiency : RemedyExecutionCapability
  canApplyInternationalFollowUpPressure : RemedyExecutionCapability
  canCreateSeparateDomesticCauseOfAction : RemedyExecutionCapability


record ImplementationChannelReceipt : Set where
  constructor implementation-channel-receipt
  field
    mechanism : Billy.ImplementationMechanism
    mechanismStrength : Billy.MechanismStrength
    strengthExact : mechanismStrength ≡ Billy.mechanismStrength mechanism
    capability : RemedyExecutionCapability
    directDomesticExecution : Bool
    sourceOrFormalReference : String

open ImplementationChannelReceipt public

executiveCompensationChannel : ImplementationChannelReceipt
executiveCompensationChannel = implementation-channel-receipt
  Billy.stateExecutiveImplementation
  Billy.availableDirect refl
  canAuthorizePayment
  true
  "DASHI implementation topology consuming Billy.mechanismStrength; executive implementation is a direct domestic route where lawful authority/funding exists."

parliamentaryAppropriationChannel : ImplementationChannelReceipt
parliamentaryAppropriationChannel = implementation-channel-receipt
  Billy.parliamentaryAppropriationOrLegislation
  Billy.availableDirect refl
  canAppropriateFunds
  true
  "Parliamentary appropriation/legislation can supply domestic authority or funding where required."

communityAgreementChannel : ImplementationChannelReceipt
communityAgreementChannel = implementation-channel-receipt
  Billy.communityNegotiatedAgreement
  Billy.availableDirect refl
  canNegotiateCommunityAgreement
  true
  "Community-negotiated agreement is a direct implementation route but does not transfer community authority to the State."

treatyFollowUpChannel : ImplementationChannelReceipt
treatyFollowUpChannel = implementation-channel-receipt
  Billy.treatyBodyFollowUpProcedure
  Billy.availableIndirect refl
  canApplyInternationalFollowUpPressure
  false
  "Human Rights Committee follow-up can increase accountability/pressure but is not a domestic execution writ."

separateDomesticRoute : ImplementationChannelReceipt
separateDomesticRoute = implementation-channel-receipt
  Billy.separateDomesticCauseOfAction
  Billy.legallySeparateRoute refl
  canCreateSeparateDomesticCauseOfAction
  false
  "A domestic cause of action, if available, is legally distinct from direct execution of the Committee's View."

------------------------------------------------------------------------
-- Realisation contract: declaration/meeting/funding != realised remedy.
------------------------------------------------------------------------

data RealisationLayer : Set where
  declaredCommitmentLayer : RealisationLayer
  lawfulAuthorityLayer : RealisationLayer
  executedMeasureLayer : RealisationLayer
  observedOutcomeLayer : RealisationLayer
  communityDefinedSuccessLayer : RealisationLayer
  feedbackCorrectionLayer : RealisationLayer


record RemedyRealisationContract : Set where
  constructor remedy-realisation-contract
  field
    coordinate : Billy.RemedyCoordinate
    requiresAuthority : Bool
    requiresExecution : Bool
    requiresObservedOutcome : Bool
    requiresCommunityDefinedSuccess : Bool
    requiresFeedbackCorrection : Bool
    closureReference : String

open RemedyRealisationContract public

compensationRealisation : RemedyRealisationContract
compensationRealisation = remedy-realisation-contract
  Billy.adequateCompensation
  true true true true true
  "Adequate compensation closes only on an authorised and executed compensation outcome adequate to the remedy consumer; announcement/funding category alone is insufficient."

consultationRealisation : RemedyRealisationContract
consultationRealisation = remedy-realisation-contract
  Billy.meaningfulConsultation
  true true true true true
  "Meaningful consultation requires more than a meeting: community-defined needs, authority/provenance preservation, implementation feedback and correction remain part of the realisation consumer."

safeExistenceRealisation : RemedyRealisationContract
safeExistenceRealisation = remedy-realisation-contract
  Billy.continuedSafeExistenceMeasures
  true true true true true
  "Protective/adaptation measures must be executed and assessed against realised safe continued existence and cultural continuity, not merely project announcement."

monitoringRealisation : RemedyRealisationContract
monitoringRealisation = remedy-realisation-contract
  Billy.monitoringAndReview
  true true true true true
  "Monitoring closes only when observations feed an effective correction loop assessed against relevant community-defined outcomes."

------------------------------------------------------------------------
-- POSIWID fixture: same declared remedy purpose, different realised state.
------------------------------------------------------------------------

data RemedySystemState : Set where
  declaredEffectiveRemedyOnly : RemedySystemState
  declaredAndRealisedEffectiveRemedy : RemedySystemState


data RemedyDeclaredPurpose : Set where
  effectiveRemedyDeclared : RemedyDeclaredPurpose

data RemedyOperationalBehaviour : Set where
  declarationWithoutFullExecution : RemedyOperationalBehaviour
  coordinatedExecutionAndCorrection : RemedyOperationalBehaviour


data RemedyRealizedEffect : Set where
  fullReparationResidualStillLive : RemedyRealizedEffect
  fullReparationRealised : RemedyRealizedEffect


data RemedyCorrectionResponse : Set where
  reportWithoutClosingResidual : RemedyCorrectionResponse
  communityFeedbackCorrectsDeficiency : RemedyCorrectionResponse


remedyDeclaredPurpose : RemedySystemState → RemedyDeclaredPurpose
remedyDeclaredPurpose _ = effectiveRemedyDeclared

remedyOperationalBehaviour : RemedySystemState → RemedyOperationalBehaviour
remedyOperationalBehaviour declaredEffectiveRemedyOnly = declarationWithoutFullExecution
remedyOperationalBehaviour declaredAndRealisedEffectiveRemedy = coordinatedExecutionAndCorrection

remedyRealizedEffect : RemedySystemState → RemedyRealizedEffect
remedyRealizedEffect declaredEffectiveRemedyOnly = fullReparationResidualStillLive
remedyRealizedEffect declaredAndRealisedEffectiveRemedy = fullReparationRealised

remedyCorrectionResponse : RemedySystemState → RemedyCorrectionResponse
remedyCorrectionResponse declaredEffectiveRemedyOnly = reportWithoutClosingResidual
remedyCorrectionResponse declaredAndRealisedEffectiveRemedy = communityFeedbackCorrectsDeficiency

remedyOperationalSystem :
  POSIWID.OperationalSystem
    RemedySystemState RemedyDeclaredPurpose RemedyOperationalBehaviour
    RemedyRealizedEffect RemedyCorrectionResponse
remedyOperationalSystem = POSIWID.operational-system
  remedyDeclaredPurpose remedyOperationalBehaviour remedyRealizedEffect remedyCorrectionResponse

sameDeclaredPurpose :
  remedyDeclaredPurpose declaredEffectiveRemedyOnly
  ≡ remedyDeclaredPurpose declaredAndRealisedEffectiveRemedy
sameDeclaredPurpose = refl

realisedEffectsDiffer :
  remedyRealizedEffect declaredEffectiveRemedyOnly
  ≡ remedyRealizedEffect declaredAndRealisedEffectiveRemedy → ⊥
realisedEffectsDiffer ()

remedyDeclarationCannotRecoverRealizedEffect :
  INF.FactorsThrough remedyDeclaredPurpose remedyRealizedEffect → ⊥
remedyDeclarationCannotRecoverRealizedEffect =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      declaredEffectiveRemedyOnly
      declaredAndRealisedEffectiveRemedy
      refl realisedEffectsDiffer)

------------------------------------------------------------------------
-- Two-Eyed Seeing / consultation: administrative completion != community
-- authority-preserving realised consultation.
------------------------------------------------------------------------

data ConsultationProcessState : Set where
  extractiveMeetingState : ConsultationProcessState
  authorityBearingCoDesignState : ConsultationProcessState


data AdministrativeConsultationSurface : Set where
  consultationRecorded : AdministrativeConsultationSurface

data CommunityConsultationOutcome : Set where
  provenanceAuthorityObligationErased : CommunityConsultationOutcome
  provenanceAuthorityObligationPreserved : CommunityConsultationOutcome


administrativeConsultationObserver :
  ConsultationProcessState → AdministrativeConsultationSurface
administrativeConsultationObserver _ = consultationRecorded

communityConsultationOutcome :
  ConsultationProcessState → CommunityConsultationOutcome
communityConsultationOutcome extractiveMeetingState = provenanceAuthorityObligationErased
communityConsultationOutcome authorityBearingCoDesignState = provenanceAuthorityObligationPreserved

consultationOutcomesDiffer :
  communityConsultationOutcome extractiveMeetingState
  ≡ communityConsultationOutcome authorityBearingCoDesignState → ⊥
consultationOutcomesDiffer ()

administrativeConsultationCannotRecoverCommunityOutcome :
  INF.FactorsThrough administrativeConsultationObserver communityConsultationOutcome → ⊥
administrativeConsultationCannotRecoverCommunityOutcome =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      extractiveMeetingState authorityBearingCoDesignState refl consultationOutcomesDiffer)

------------------------------------------------------------------------
-- Existing Indigenous-knowledge theorem surfaces are inherited exactly.
------------------------------------------------------------------------

sameExtractedPropositionDoesNotRecoverProvenance :
  INF.FactorsThrough IK.extractedProposition IK.carrierProvenance → ⊥
sameExtractedPropositionDoesNotRecoverProvenance = IK.propositionCannotRecoverProvenance

sameExtractedPropositionDoesNotRecoverAuthority :
  INF.FactorsThrough IK.extractedProposition IK.authority → ⊥
sameExtractedPropositionDoesNotRecoverAuthority = IK.propositionCannotRecoverAuthority

sameExtractedPropositionDoesNotRecoverPermission :
  INF.FactorsThrough IK.extractedProposition IK.permission → ⊥
sameExtractedPropositionDoesNotRecoverPermission = IK.propositionCannotRecoverPermission

sameExtractedPropositionDoesNotRecoverObligation :
  INF.FactorsThrough IK.extractedProposition IK.obligation → ⊥
sameExtractedPropositionDoesNotRecoverObligation = IK.propositionCannotRecoverObligation

sharedObservationDoesNotRecoverKnowledgeProvenance :
  INF.FactorsThrough TwoEyed.observeKnowledgeHistory TwoEyed.provenance → ⊥
sharedObservationDoesNotRecoverKnowledgeProvenance =
  TwoEyed.sharedObservationDoesNotRecoverProvenance

------------------------------------------------------------------------
-- Coordinate-sensitive practical prospects: no fake scalar probability.
------------------------------------------------------------------------

record PracticalProspectReceipt : Set where
  constructor practical-prospect-receipt
  field
    coordinate : Billy.RemedyCoordinate
    publicImplementationState : Billy.PublicImplementationState
    publicStateExact : publicImplementationState ≡ Billy.publicImplementationState coordinate
    practicalProspect : Billy.PracticalProspect
    prospectExact : practicalProspect ≡ Billy.prospectFor coordinate
    directMechanismExists : Bool
    publicEvidenceFullyClosesCoordinate : Bool
    basisReference : String

open PracticalProspectReceipt public

compensationProspect : PracticalProspectReceipt
compensationProspect = practical-prospect-receipt
  Billy.adequateCompensation
  Billy.publicReceiptNotRecovered refl
  Billy.politicallyContingentProspect refl
  true
  false
  "Direct executive/appropriation routes exist in principle, but the current public atlas has not recovered a compensation receipt; no numerical probability is inferred."

consultationProspect : PracticalProspectReceipt
consultationProspect = practical-prospect-receipt
  Billy.meaningfulConsultation
  Billy.publicEvidencePresent refl
  Billy.comparativelyStrongProspect refl
  true
  false
  "Public evidence of consultation exists, but administrative evidence of consultation does not by itself establish authority-bearing/community-defined realised adequacy."

safeExistenceProspect : PracticalProspectReceipt
safeExistenceProspect = practical-prospect-receipt
  Billy.continuedSafeExistenceMeasures
  Billy.publicEvidencePresent refl
  Billy.comparativelyStrongProspect refl
  true
  false
  "Adaptation/protective implementation evidence exists; realised continued safe existence remains the consumer rather than expenditure alone."

------------------------------------------------------------------------
-- BIDI: unresolved coordinate -> next evidence/action producer.
------------------------------------------------------------------------

data RemedyNextProducer : Set where
  recoverCompensationExecutionReceipt : RemedyNextProducer
  recoverCommunityDefinedNeedsReceipt : RemedyNextProducer
  recoverCommunityOutcomeAssessment : RemedyNextProducer
  recoverCorrectionLoopReceipt : RemedyNextProducer
  recoverPreventionOutcomeReceipt : RemedyNextProducer


nextProducer : Billy.RemedyCoordinate → RemedyNextProducer
nextProducer Billy.adequateCompensation = recoverCompensationExecutionReceipt
nextProducer Billy.meaningfulConsultation = recoverCommunityDefinedNeedsReceipt
nextProducer Billy.communityNeedsAssessment = recoverCommunityDefinedNeedsReceipt
nextProducer Billy.continuedSafeExistenceMeasures = recoverCommunityOutcomeAssessment
nextProducer Billy.monitoringAndReview = recoverCorrectionLoopReceipt
nextProducer Billy.correctionOfDeficiencies = recoverCorrectionLoopReceipt
nextProducer Billy.preventionOfSimilarViolations = recoverPreventionOutcomeReceipt
nextProducer Billy.publicationAndDissemination = recoverCommunityOutcomeAssessment

compensationRoutesToExecutionReceipt :
  nextProducer Billy.adequateCompensation ≡ recoverCompensationExecutionReceipt
compensationRoutesToExecutionReceipt = refl

monitoringRoutesToCorrectionLoop :
  nextProducer Billy.monitoringAndReview ≡ recoverCorrectionLoopReceipt
monitoringRoutesToCorrectionLoop = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data StateReportClosesRealisedRemedy : Set where
data ConsultationMeetingProvesAuthorityBearingConsultation : Set where
data FundingAmountProvesSafeContinuedExistence : Set where
data HumanRightsCommitteeViewExecutesItselfDomestically : Set where
data StrongProspectMeansGuaranteedOutcome : Set where
data CommunityFeedbackTransfersCommunityAuthorityToState : Set where

stateReportDoesNotCloseRealisedRemedy : StateReportClosesRealisedRemedy → ⊥
stateReportDoesNotCloseRealisedRemedy ()

meetingDoesNotProveAuthorityBearingConsultation :
  ConsultationMeetingProvesAuthorityBearingConsultation → ⊥
meetingDoesNotProveAuthorityBearingConsultation ()

fundingDoesNotProveSafeContinuedExistence : FundingAmountProvesSafeContinuedExistence → ⊥
fundingDoesNotProveSafeContinuedExistence ()

committeeViewDoesNotExecuteItself : HumanRightsCommitteeViewExecutesItselfDomestically → ⊥
committeeViewDoesNotExecuteItself ()

prospectIsNotGuarantee : StrongProspectMeansGuaranteedOutcome → ⊥
prospectIsNotGuarantee ()

feedbackDoesNotTransferAuthority : CommunityFeedbackTransfersCommunityAuthorityToState → ⊥
feedbackDoesNotTransferAuthority ()
