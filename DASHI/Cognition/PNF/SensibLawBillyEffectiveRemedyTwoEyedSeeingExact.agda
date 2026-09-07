module DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact where

------------------------------------------------------------------------
-- BILLY ET AL v AUSTRALIA / EFFECTIVE REMEDY / TWO-EYED SEEING
--
-- Source boundaries:
--   Human Rights Committee, Billy and others v Australia,
--   CCPR/C/135/D/3624/2019, Views adopted 21 July 2022.
--   Australian Government response published 30 March 2023.
--   Human Rights Committee List of Issues Prior to Reporting for Australia's
--   seventh periodic report, adopted 2025.
--   Australian consultation draft seventh periodic report, 2026.
--
-- The Committee's Views, Australia's response, later treaty-body follow-up,
-- and DASHI's implementation audit are separately typed.  This file does not
-- silently convert a treaty-body View into a domestic execution writ, and it
-- does not infer that absence of a public compensation receipt proves that no
-- compensation has ever been paid.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.KimmererBraidingAcknowledgement as Sweetgrass
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IndigenousKnowledge
import DASHI.Core.DeclaredRealizedIntegrityResidualExact as DeclaredRealized

------------------------------------------------------------------------
-- Authority / proposition kinds.
------------------------------------------------------------------------

data BillySourceKind : Set where
  humanRightsCommitteeView : BillySourceKind
  statePartyResponse : BillySourceKind
  treatyBodyFollowUpQuestion : BillySourceKind
  statePeriodicReportDraft : BillySourceKind
  dashiImplementationAudit : BillySourceKind


record BillySourceProposition : Set where
  constructor billy-source-proposition
  field
    sourceKind : BillySourceKind
    propositionReference : String
    sourceReference : String
    sourceSaysThisDirectly : Bool
    worldTruthAdjudicatedByThisReceipt : Bool
    worldTruthAdjudicatedByThisReceiptIsFalse :
      worldTruthAdjudicatedByThisReceipt ≡ false

open BillySourceProposition public

committeeViolationFinding : BillySourceProposition
committeeViolationFinding = billy-source-proposition
  humanRightsCommitteeView
  "The Human Rights Committee found violations of ICCPR articles 17 and 27 in Billy and others v Australia."
  "CCPR/C/135/D/3624/2019, paras 9-12"
  true
  false refl

committeeFullReparationRequirement : BillySourceProposition
committeeFullReparationRequirement = billy-source-proposition
  humanRightsCommitteeView
  "Effective remedy requires full reparation, including adequate compensation, meaningful consultations/needs assessment, measures securing continued safe existence on the islands, monitoring/review, prompt correction of deficiencies, and prevention of similar violations."
  "CCPR/C/135/D/3624/2019, para 11"
  true
  false refl

committee180DayFollowUp : BillySourceProposition
committee180DayFollowUp = billy-source-proposition
  humanRightsCommitteeView
  "The Committee requested information within 180 days on measures taken to give effect to its Views."
  "CCPR/C/135/D/3624/2019, para 12"
  true
  false refl

australiaConsultationAndAdaptationResponse : BillySourceProposition
australiaConsultationAndAdaptationResponse = billy-source-proposition
  statePartyResponse
  "Australia reported consultations with authors and Torres Strait communities, adaptation/funding measures, and commitments to monitoring/review."
  "Australian Government Response to Billy et al v Australia, 30 March 2023"
  true
  false refl

australiaRemedyFraming : BillySourceProposition
australiaRemedyFraming = billy-source-proposition
  statePartyResponse
  "Australia framed the most appropriate remedies around collaboration with First Nations/Torres Strait Islander communities, reform and funding, while committing to adaptation measures and monitoring/review."
  "Australian Government Response, paras 57-60"
  true
  false refl

committee2025ImplementationQuestion : BillySourceProposition
committee2025ImplementationQuestion = billy-source-proposition
  treatyBodyFollowUpQuestion
  "The Committee asked Australia to report mechanisms for implementing Optional Protocol Views, including Billy, so as to guarantee victims an effective remedy."
  "CCPR/C/AUS/QPR/7, List of Issues Prior to Reporting, 2025"
  true
  false refl

australia2026PeriodicDraft : BillySourceProposition
australia2026PeriodicDraft = billy-source-proposition
  statePeriodicReportDraft
  "Australia's 2026 consultation draft records continuing collaboration with First Nations and Torres Strait Islander peoples and funding of climate-response efforts in the Torres Strait."
  "Consultation draft: Australia's seventh periodic report under the ICCPR, 2026"
  true
  false refl

------------------------------------------------------------------------
-- Remedy coordinates are conjunctive; one does not substitute for another.
------------------------------------------------------------------------

data RemedyCoordinate : Set where
  adequateCompensation : RemedyCoordinate
  meaningfulConsultation : RemedyCoordinate
  communityNeedsAssessment : RemedyCoordinate
  continuedSafeExistenceMeasures : RemedyCoordinate
  monitoringAndReview : RemedyCoordinate
  correctionOfDeficiencies : RemedyCoordinate
  preventionOfSimilarViolations : RemedyCoordinate
  publicationAndDissemination : RemedyCoordinate


data PublicImplementationState : Set where
  publicEvidencePresent : PublicImplementationState
  publicEvidencePartial : PublicImplementationState
  publicReceiptNotRecovered : PublicImplementationState
  sourceDoesNotAddress : PublicImplementationState


publicImplementationState : RemedyCoordinate → PublicImplementationState
publicImplementationState adequateCompensation = publicReceiptNotRecovered
publicImplementationState meaningfulConsultation = publicEvidencePresent
publicImplementationState communityNeedsAssessment = publicEvidencePartial
publicImplementationState continuedSafeExistenceMeasures = publicEvidencePresent
publicImplementationState monitoringAndReview = publicEvidencePresent
publicImplementationState correctionOfDeficiencies = publicEvidencePartial
publicImplementationState preventionOfSimilarViolations = publicEvidencePartial
publicImplementationState publicationAndDissemination = publicEvidencePresent

compensationReceiptNotRecovered :
  publicImplementationState adequateCompensation ≡ publicReceiptNotRecovered
compensationReceiptNotRecovered = refl

consultationEvidencePresent :
  publicImplementationState meaningfulConsultation ≡ publicEvidencePresent
consultationEvidencePresent = refl

adaptationEvidencePresent :
  publicImplementationState continuedSafeExistenceMeasures ≡ publicEvidencePresent
adaptationEvidencePresent = refl

------------------------------------------------------------------------
-- Full reparation is not discharged by one visible coordinate.
------------------------------------------------------------------------

data FullReparationStatus : Set where
  fullReparationClosed : FullReparationStatus
  fullReparationResidualLive : FullReparationStatus


currentPublicFullReparationStatus : FullReparationStatus
currentPublicFullReparationStatus = fullReparationResidualLive

currentPublicFullReparationResidualIsLive :
  currentPublicFullReparationStatus ≡ fullReparationResidualLive
currentPublicFullReparationResidualIsLive = refl

------------------------------------------------------------------------
-- Enforcement / implementation topology.
------------------------------------------------------------------------

data ImplementationMechanism : Set where
  stateExecutiveImplementation : ImplementationMechanism
  parliamentaryAppropriationOrLegislation : ImplementationMechanism
  treatyBodyFollowUpProcedure : ImplementationMechanism
  periodicReportingAndQuestioning : ImplementationMechanism
  publicPoliticalAccountability : ImplementationMechanism
  communityNegotiatedAgreement : ImplementationMechanism
  separateDomesticCauseOfAction : ImplementationMechanism
  directTreatyBodyDomesticExecutionWrit : ImplementationMechanism


data MechanismStrength : Set where
  availableDirect : MechanismStrength
  availableIndirect : MechanismStrength
  legallySeparateRoute : MechanismStrength
  unavailableByDefault : MechanismStrength


mechanismStrength : ImplementationMechanism → MechanismStrength
mechanismStrength stateExecutiveImplementation = availableDirect
mechanismStrength parliamentaryAppropriationOrLegislation = availableDirect
mechanismStrength treatyBodyFollowUpProcedure = availableIndirect
mechanismStrength periodicReportingAndQuestioning = availableIndirect
mechanismStrength publicPoliticalAccountability = availableIndirect
mechanismStrength communityNegotiatedAgreement = availableDirect
mechanismStrength separateDomesticCauseOfAction = legallySeparateRoute
mechanismStrength directTreatyBodyDomesticExecutionWrit = unavailableByDefault

noAutomaticDomesticExecutionWrit :
  mechanismStrength directTreatyBodyDomesticExecutionWrit ≡ unavailableByDefault
noAutomaticDomesticExecutionWrit = refl

stateCanImplementDirectly :
  mechanismStrength stateExecutiveImplementation ≡ availableDirect
stateCanImplementDirectly = refl

followUpIsIndirectLeverage :
  mechanismStrength treatyBodyFollowUpProcedure ≡ availableIndirect
followUpIsIndirectLeverage = refl

------------------------------------------------------------------------
-- Practical odds are coordinate-sensitive, not one scalar probability.
------------------------------------------------------------------------

data PracticalProspect : Set where
  comparativelyStrongProspect : PracticalProspect
  politicallyContingentProspect : PracticalProspect
  structurallyWeakCoerciveProspect : PracticalProspect
  insufficientPublicEvidenceForEstimate : PracticalProspect


prospectFor : RemedyCoordinate → PracticalProspect
prospectFor meaningfulConsultation = comparativelyStrongProspect
prospectFor continuedSafeExistenceMeasures = comparativelyStrongProspect
prospectFor monitoringAndReview = comparativelyStrongProspect
prospectFor adequateCompensation = politicallyContingentProspect
prospectFor communityNeedsAssessment = politicallyContingentProspect
prospectFor correctionOfDeficiencies = politicallyContingentProspect
prospectFor preventionOfSimilarViolations = politicallyContingentProspect
prospectFor publicationAndDissemination = comparativelyStrongProspect

compensationIsPoliticallyContingent :
  prospectFor adequateCompensation ≡ politicallyContingentProspect
compensationIsPoliticallyContingent = refl

------------------------------------------------------------------------
-- Two-Eyed Seeing: consultation is not extraction into one state observer.
------------------------------------------------------------------------

knowledgeCoordinationBoundary : TwoEyed.KimmererTwoEyedSeeingBoundary
knowledgeCoordinationBoundary = TwoEyed.canonicalKimmererTwoEyedSeeingBoundary

sharedObservationDoesNotFuseKnowledgeHistory :
  TwoEyed.sharedObservationMeansSameEpistemicHistory knowledgeCoordinationBoundary ≡ false
sharedObservationDoesNotFuseKnowledgeHistory = refl

coordinationDoesNotRequireFusion :
  TwoEyed.coordinatedUseRequiresEpistemicFusion knowledgeCoordinationBoundary ≡ false
coordinationDoesNotRequireFusion = refl

sweetgrassAcknowledgement : Sweetgrass.KimmererBraidingAcknowledgement
sweetgrassAcknowledgement = Sweetgrass.canonicalKimmererBraidingAcknowledgement

braidingKeepsDistinctWarrants : String
braidingKeepsDistinctWarrants = TwoEyed.braidingReading

------------------------------------------------------------------------
-- Consultation adequacy must preserve relation, authority and obligation.
------------------------------------------------------------------------

data ConsultationCoordinate : Set where
  observedNeed : ConsultationCoordinate
  placeRelation : ConsultationCoordinate
  communityAuthority : ConsultationCoordinate
  knowledgeProvenance : ConsultationCoordinate
  permissionAndProtocol : ConsultationCoordinate
  reciprocalObligation : ConsultationCoordinate
  implementationFeedback : ConsultationCoordinate


data ConsultationAdequacy : Set where
  extractiveConsultation : ConsultationAdequacy
  provenancePreservingConsultation : ConsultationAdequacy
  authorityBearingConsultation : ConsultationAdequacy
  reciprocalRemedyCoDesign : ConsultationAdequacy


record RemedyConsultationBoundary : Set where
  constructor remedy-consultation-boundary
  field
    hearingCommunityObservationEqualsTransferringAuthority : Bool
    hearingCommunityObservationEqualsTransferringAuthorityIsFalse :
      hearingCommunityObservationEqualsTransferringAuthority ≡ false
    consultationMayEraseProvenanceAndObligation : Bool
    consultationMayEraseProvenanceAndObligationIsTrue :
      consultationMayEraseProvenanceAndObligation ≡ true
    adequateConsultationRequiresCommunityDefinedNeeds : Bool
    adequateConsultationRequiresCommunityDefinedNeedsIsTrue :
      adequateConsultationRequiresCommunityDefinedNeeds ≡ true
    monitoringRequiresCommunityFeedbackLoop : Bool
    monitoringRequiresCommunityFeedbackLoopIsTrue :
      monitoringRequiresCommunityFeedbackLoop ≡ true
    scientificGovernmentObservationExhaustsCountryKnowledge : Bool
    scientificGovernmentObservationExhaustsCountryKnowledgeIsFalse :
      scientificGovernmentObservationExhaustsCountryKnowledge ≡ false
    remedyCanBeCoordinatedWithoutEpistemicFusion : Bool
    remedyCanBeCoordinatedWithoutEpistemicFusionIsTrue :
      remedyCanBeCoordinatedWithoutEpistemicFusion ≡ true

open RemedyConsultationBoundary public

canonicalRemedyConsultationBoundary : RemedyConsultationBoundary
canonicalRemedyConsultationBoundary = remedy-consultation-boundary
  false refl
  true refl
  true refl
  true refl
  false refl
  true refl

------------------------------------------------------------------------
-- "A system is what it does": implementation is measured by realised remedy.
------------------------------------------------------------------------

record RemedyOperationalSemantics : Set where
  constructor remedy-operational-semantics
  field
    declaredCommitment : String
    realisedImplementation : String
    declarationAloneClosesRemedy : Bool
    declarationAloneClosesRemedyIsFalse : declarationAloneClosesRemedy ≡ false
    fundingAnnouncementAloneClosesCompensationCoordinate : Bool
    fundingAnnouncementAloneClosesCompensationCoordinateIsFalse :
      fundingAnnouncementAloneClosesCompensationCoordinate ≡ false
    consultationMeetingAloneClosesNeedsAssessment : Bool
    consultationMeetingAloneClosesNeedsAssessmentIsFalse :
      consultationMeetingAloneClosesNeedsAssessment ≡ false
    realisedCommunitySafetyAndCulturalContinuityMatter : Bool
    realisedCommunitySafetyAndCulturalContinuityMatterIsTrue :
      realisedCommunitySafetyAndCulturalContinuityMatter ≡ true
    implementationMustBeMonitoredAgainstCommunityDefinedOutcome : Bool
    implementationMustBeMonitoredAgainstCommunityDefinedOutcomeIsTrue :
      implementationMustBeMonitoredAgainstCommunityDefinedOutcome ≡ true

open RemedyOperationalSemantics public

canonicalRemedyOperationalSemantics : RemedyOperationalSemantics
canonicalRemedyOperationalSemantics = remedy-operational-semantics
  "Australia states commitments to collaboration, funding, adaptation and monitoring."
  "The operative consumer is whether each Committee remedy coordinate is actually realised for the authors and communities, including compensation, safe continued existence, cultural continuity and correction of deficiencies."
  false refl
  false refl
  false refl
  true refl
  true refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data ConsultationEqualsFullReparation : Set where
data AdaptationFundingEqualsCompensation : Set where
data NoPublicCompensationReceiptProvesNoPaymentEver : Set where
data TwoEyedSeeingTransfersCommunityAuthorityToState : Set where
data TreatyBodyViewEqualsDomesticExecutionOrder : Set where
data GovernmentCommitmentEqualsRealisedRemedy : Set where

consultationDoesNotEqualFullReparation : ConsultationEqualsFullReparation → ⊥
consultationDoesNotEqualFullReparation ()

adaptationFundingDoesNotEqualCompensation : AdaptationFundingEqualsCompensation → ⊥
adaptationFundingDoesNotEqualCompensation ()

missingPublicReceiptDoesNotProveNonpayment :
  NoPublicCompensationReceiptProvesNoPaymentEver → ⊥
missingPublicReceiptDoesNotProveNonpayment ()

twoEyedSeeingDoesNotTransferAuthority : TwoEyedSeeingTransfersCommunityAuthorityToState → ⊥
twoEyedSeeingDoesNotTransferAuthority ()

committeeViewDoesNotBecomeDomesticExecutionOrder :
  TreatyBodyViewEqualsDomesticExecutionOrder → ⊥
committeeViewDoesNotBecomeDomesticExecutionOrder ()

declarationDoesNotEqualRealisedRemedy : GovernmentCommitmentEqualsRealisedRemedy → ⊥
declarationDoesNotEqualRealisedRemedy ()
