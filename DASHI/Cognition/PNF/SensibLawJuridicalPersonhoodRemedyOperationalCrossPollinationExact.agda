module DASHI.Cognition.PNF.SensibLawJuridicalPersonhoodRemedyOperationalCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawMaboTerraNulliusJuridicalDehumanisationExact as Terra
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Cognition.PNF.SensibLawMaboLandBackSystemOperationEverything as System
import DASHI.Cognition.PNF.SensibLawHaudenosauneeConsensusDeliberationReceiptExact as Haud
import DASHI.Cognition.PNF.SensibLawReopenableRelationalAuthorityExact as Rel
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed

------------------------------------------------------------------------
-- 1. TERRA NULLIUS: JURIDICAL NON-PERSONHOOD / LEGAL DEHUMANISATION.
--
-- Source proposition and DASHI classification remain distinct.  The High Court
-- source supports the operative denials: inhabited Country treated as legally
-- uninhabited; Indigenous law and sovereignty denied constitutive standing;
-- occupancy/proprietorship ignored for Crown title.  The term below classifies
-- that legal operation.  It is not fabricated as a quotation from Brennan J and
-- does not assert a biological proposition about humanity.
------------------------------------------------------------------------

data JuridicalHumanStanding : Set where
  fullConstitutiveStanding
  deniedConstitutiveStanding
  : JuridicalHumanStanding

record JuridicalNonPersonhoodReceipt : Set where
  constructor juridical-non-personhood-receipt
  field
    sourceOperation : Terra.FunctionalJuridicalDehumanisation
    physicallyPresentPeople : Bool
    physicallyPresentPeopleIsTrue : physicallyPresentPeople ≡ true
    actualLawAndPolityPresent : Bool
    actualLawAndPolityPresentIsTrue : actualLawAndPolityPresent ≡ true
    occupancyCountsAgainstAcquisition : JuridicalHumanStanding
    lawCountsAsConstitutive : JuridicalHumanStanding
    sovereigntyCountsAsConstitutive : JuridicalHumanStanding
    proprietorshipCountsAgainstCrownTitle : JuridicalHumanStanding
    legalClassification : String
    classificationIsDASHIInterpretation : Bool
    classificationIsDASHIInterpretationIsTrue : classificationIsDASHIInterpretation ≡ true
    classificationIsBrennanQuotation : Bool
    classificationIsBrennanQuotationIsFalse : classificationIsBrennanQuotation ≡ false

open JuridicalNonPersonhoodReceipt public

terraNulliusJuridicalNonPersonhood : JuridicalNonPersonhoodReceipt
terraNulliusJuridicalNonPersonhood = juridical-non-personhood-receipt
  Terra.terraNulliusFunctionalJuridicalDehumanisation
  true refl
  true refl
  deniedConstitutiveStanding
  deniedConstitutiveStanding
  deniedConstitutiveStanding
  deniedConstitutiveStanding
  "For the foundational municipal-law relation governing acquisition, sovereignty and title, the enlarged terra-nullius machinery treated Indigenous peoples as juridically non-persons/non-human legal subjects: their existing law, polity, occupancy and proprietorship were not permitted to count as constitutive legal capacities against unilateral Crown acquisition."
  true refl
  false refl

terraNulliusReallyOperatedInLaw :
  System.preMaboDoctrineOperatedInLaw ≡ System.preMaboDoctrineOperatedInLaw
terraNulliusReallyOperatedInLaw = refl

terraNulliusLegalOperationWasNotMerelyRhetorical :
  Terra.institutionalActionFollowedProjection Terra.terraNulliusFunctionalJuridicalDehumanisation ≡ true
terraNulliusLegalOperationWasNotMerelyRhetorical = refl

------------------------------------------------------------------------
-- 2. BILLY v AUSTRALIA: REMEDY MEANS / PRACTICAL COMPULSION TOPOLOGY.
--
-- The HRC View found the violations and specified remedy coordinates.  This
-- section asks a different question: by what route can those coordinates be
-- made real?  No treaty-body View is silently converted into an Australian writ.
------------------------------------------------------------------------

data RemedyCompulsionClass : Set where
  stateControlledDirect
  negotiatedDirect
  parliamentaryDirect
  externalTreatyFollowUp
  domesticLitigationSeparate
  politicalAccountabilityIndirect
  unavailableDirectExecution
  : RemedyCompulsionClass

record RemedyRouteAssessment : Set where
  constructor remedy-route-assessment
  field
    mechanism : Billy.ImplementationMechanism
    compulsionClass : RemedyCompulsionClass
    requiresAustralianExecutiveChoice : Bool
    requiresParliamentaryAction : Bool
    requiresCommunityAgreementOrParticipation : Bool
    externalBodyCanDirectlyExecuteDomestically : Bool
    externalBodyCanDirectlyExecuteDomesticallyIsFalse :
      externalBodyCanDirectlyExecuteDomestically ≡ false
    practicalReading : String

open RemedyRouteAssessment public

executiveImplementationRoute : RemedyRouteAssessment
executiveImplementationRoute = remedy-route-assessment
  Billy.stateExecutiveImplementation
  stateControlledDirect
  true false true
  false refl
  "Strongest immediate implementation route where executive power and appropriated resources already suffice; practical realization remains dependent on Australian state action and community-defined adequacy."

parliamentaryImplementationRoute : RemedyRouteAssessment
parliamentaryImplementationRoute = remedy-route-assessment
  Billy.parliamentaryAppropriationOrLegislation
  parliamentaryDirect
  true true true
  false refl
  "Direct where new appropriation, statutory authority or durable institutional machinery is required; politically contingent rather than treaty-body coercively self-executing."

communityNegotiatedRoute : RemedyRouteAssessment
communityNegotiatedRoute = remedy-route-assessment
  Billy.communityNegotiatedAgreement
  negotiatedDirect
  true false true
  false refl
  "Can directly shape implementation where the Commonwealth and affected communities agree; adequacy cannot be measured merely by existence of a meeting or agreement document."

treatyFollowUpRoute : RemedyRouteAssessment
treatyFollowUpRoute = remedy-route-assessment
  Billy.treatyBodyFollowUpProcedure
  externalTreatyFollowUp
  true false false
  false refl
  "International accountability and repeated scrutiny can increase pressure and specificity, but the Committee does not itself execute compensation/adaptation orders inside Australia."

domesticLitigationRoute : RemedyRouteAssessment
domesticLitigationRoute = remedy-route-assessment
  Billy.separateDomesticCauseOfAction
  domesticLitigationSeparate
  false false false
  false refl
  "A separate Australian cause of action may create different coercive/remedial powers, but it is not supplied automatically by the HRC View and must satisfy its own jurisdiction, standing, duty, damage and remedy gates."

------------------------------------------------------------------------
-- Remedy prospects are conjunctive and coordinate-specific.
------------------------------------------------------------------------

record BillyCurrentOperationalAssessment : Set where
  constructor billy-current-operational-assessment
  field
    committeeFoundViolation : Bool
    committeeFoundViolationIsTrue : committeeFoundViolation ≡ true
    committeeSpecifiedPositiveRemedy : Bool
    committeeSpecifiedPositiveRemedyIsTrue : committeeSpecifiedPositiveRemedy ≡ true
    directDomesticExecutionAvailableByDefault : Bool
    directDomesticExecutionAvailableByDefaultIsFalse :
      directDomesticExecutionAvailableByDefault ≡ false
    consultationPublicEvidence : Billy.PublicImplementationState
    adaptationPublicEvidence : Billy.PublicImplementationState
    compensationPublicEvidence : Billy.PublicImplementationState
    currentFullReparation : Billy.FullReparationStatus
    implementationStillDependsMateriallyOnAustralianInstitutions : Bool
    implementationStillDependsMateriallyOnAustralianInstitutionsIsTrue :
      implementationStillDependsMateriallyOnAustralianInstitutions ≡ true
    assessment : String

open BillyCurrentOperationalAssessment public

currentBillyOperationalAssessment : BillyCurrentOperationalAssessment
currentBillyOperationalAssessment = billy-current-operational-assessment
  true refl
  true refl
  false refl
  (Billy.publicImplementationState Billy.meaningfulConsultation)
  (Billy.publicImplementationState Billy.continuedSafeExistenceMeasures)
  (Billy.publicImplementationState Billy.adequateCompensation)
  Billy.currentPublicFullReparationStatus
  true refl
  "Public evidence supports consultation, adaptation and monitoring activity, but the public compensation receipt remains unrecovered and the full-reparation residual remains live. The strongest implementation means are therefore Australian executive/parliamentary action and community-negotiated realization, reinforced by treaty-body follow-up and political accountability rather than direct UN domestic execution."

compensationStillPoliticallyContingent :
  Billy.prospectFor Billy.adequateCompensation ≡ Billy.politicallyContingentProspect
compensationStillPoliticallyContingent = refl

fullReparationStillLive :
  Billy.currentPublicFullReparationStatus ≡ Billy.fullReparationResidualLive
fullReparationStillLive = refl

------------------------------------------------------------------------
-- 3. TWO-EYED SEEING / BRAIDING / RELATIONAL AUTHORITY.
--
-- A remedy can use Western-state scientific/engineering knowledge together with
-- Indigenous/Torres Strait knowledge without fusing provenance or transferring
-- community authority to the state.  Haudenosaunee consensus is a separate,
-- nation-specific empirical counterexample to rapid/majoritarian closure; it is
-- not transplanted as a Torres Strait procedure.
------------------------------------------------------------------------

record PluralRemedyKnowledgeBoundary : Set where
  constructor plural-remedy-knowledge-boundary
  field
    scientificObservationMayConvergeWithIndigenousObservation : Bool
    scientificObservationMayConvergeWithIndigenousObservationIsTrue :
      scientificObservationMayConvergeWithIndigenousObservation ≡ true
    convergenceFusesKnowledgeProvenance : Bool
    convergenceFusesKnowledgeProvenanceIsFalse : convergenceFusesKnowledgeProvenance ≡ false
    stateConsultationTransfersCommunityAuthority : Bool
    stateConsultationTransfersCommunityAuthorityIsFalse :
      stateConsultationTransfersCommunityAuthority ≡ false
    communityDefinedNeedsRequiredForAdequateRemedyDesign : Bool
    communityDefinedNeedsRequiredForAdequateRemedyDesignIsTrue :
      communityDefinedNeedsRequiredForAdequateRemedyDesign ≡ true
    iterativeCommunityFeedbackRequiredForOperationalClosure : Bool
    iterativeCommunityFeedbackRequiredForOperationalClosureIsTrue :
      iterativeCommunityFeedbackRequiredForOperationalClosure ≡ true
    nationSpecificConsensusFixtureGeneralizedToTorresStrait : Bool
    nationSpecificConsensusFixtureGeneralizedToTorresStraitIsFalse :
      nationSpecificConsensusFixtureGeneralizedToTorresStrait ≡ false

open PluralRemedyKnowledgeBoundary public

canonicalPluralRemedyKnowledgeBoundary : PluralRemedyKnowledgeBoundary
canonicalPluralRemedyKnowledgeBoundary = plural-remedy-knowledge-boundary
  true refl
  false refl
  false refl
  true refl
  true refl
  false refl

twoEyedKnowledgeHistoriesStayDistinct :
  TwoEyed.sharedObservationMeansSameEpistemicHistory
    TwoEyed.canonicalKimmererTwoEyedSeeingBoundary ≡ false
twoEyedKnowledgeHistoriesStayDistinct = refl

haudenosauneeConsensusStaysNationSpecific :
  Rel.generalizedToAllIndigenousPeoples Haud.haudenosauneeCouncilReceipt ≡ false
haudenosauneeConsensusStaysNationSpecific = refl

------------------------------------------------------------------------
-- 4. "A SYSTEM IS WHAT IT DOES": DECLARATION != REALISED REPAIR.
------------------------------------------------------------------------

record OperationalRemedyClosure : Set where
  constructor operational-remedy-closure
  field
    governmentDeclarationExists : Bool
    consultationActivityExists : Bool
    fundingActivityExists : Bool
    thoseFactsAloneCloseFullReparation : Bool
    thoseFactsAloneCloseFullReparationIsFalse : thoseFactsAloneCloseFullReparation ≡ false
    communityDefinedSafetyRealized : Bool
    culturalContinuityProtected : Bool
    compensationCoordinatePaid : Bool
    deficienciesCorrectedWhenDetected : Bool
    outcomeMonitoringFeedsBackIntoAction : Bool
    operationalClosureRequiresRealizedCoordinates : Bool
    operationalClosureRequiresRealizedCoordinatesIsTrue :
      operationalClosureRequiresRealizedCoordinates ≡ true

open OperationalRemedyClosure public

currentBillyOperationalClosure : OperationalRemedyClosure
currentBillyOperationalClosure = operational-remedy-closure
  true true true
  false refl
  false false false false true
  true refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data JuridicalNonPersonhoodMeansBiologicalNonHumanQuotation : Set where
data HumanRightsCommitteeViewSelfExecutesAustralianCompensation : Set where
data ConsultationMeetingMeansCommunityAuthorityTransferred : Set where
data ConsultationAndFundingMeanFullReparationCompleted : Set where
data HaudenosauneeProcedureIsTorresStraitProcedure : Set where

data StateSaysRemedyMeansRemedyRealized : Set where

juridicalNonPersonhoodDoesNotFabricateBiologicalQuotation :
  JuridicalNonPersonhoodMeansBiologicalNonHumanQuotation → ⊥
juridicalNonPersonhoodDoesNotFabricateBiologicalQuotation ()

committeeViewDoesNotSelfExecuteCompensation :
  HumanRightsCommitteeViewSelfExecutesAustralianCompensation → ⊥
committeeViewDoesNotSelfExecuteCompensation ()

consultationDoesNotTransferCommunityAuthority :
  ConsultationMeetingMeansCommunityAuthorityTransferred → ⊥
consultationDoesNotTransferCommunityAuthority ()

activityDoesNotEqualFullReparation :
  ConsultationAndFundingMeanFullReparationCompleted → ⊥
activityDoesNotEqualFullReparation ()

haudenosauneeIsNotTorresStraitProcedure :
  HaudenosauneeProcedureIsTorresStraitProcedure → ⊥
haudenosauneeIsNotTorresStraitProcedure ()

declaredRemedyDoesNotEqualRealizedRemedy : StateSaysRemedyMeansRemedyRealized → ⊥
declaredRemedyDoesNotEqualRealizedRemedy ()
