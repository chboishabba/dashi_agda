module DASHI.Law.SensibLawWoogarooBartyRepresentativeFirstOutreachExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooBartyOutreachExact as Outreach
import DASHI.Law.SensibLawWoogarooBartyStewardshipCrossPollinationExact as Stewardship

------------------------------------------------------------------------
-- REPRESENTATIVE-FIRST OUTREACH ROUTING
--
-- Current public-source carrier:
-- NC Management lists Ashleigh Barty as a client and states that its services
-- include talent representation, sponsorship, brand strategy and media/PR.
-- It publishes info@ncmanagement.com.au for talent enquiries/bookings.
--
-- This module therefore routes the first contact through the authorised public
-- management channel rather than around it.  It does not assert that NC
-- Management has accepted the request or that any specific employee is the
-- correct recipient for this matter until the agency says so.
------------------------------------------------------------------------

data ContactSurface : Set where
  authorisedManagementAgency : ContactSurface
  foundationPublicContact : ContactSurface
  directPersonalContact : ContactSurface
  publicSocialMedia : ContactSurface


data ContactProducer : Set where
  managementTriageProducer : ContactProducer
  foundationTriageProducer : ContactProducer
  directPersonalProducer : ContactProducer
  socialMediaProducer : ContactProducer

producerForSurface : ContactSurface → ContactProducer
producerForSurface authorisedManagementAgency = managementTriageProducer
producerForSurface foundationPublicContact = foundationTriageProducer
producerForSurface directPersonalContact = directPersonalProducer
producerForSurface publicSocialMedia = socialMediaProducer

record PublicRepresentativeRoute : Set where
  constructor publicRepresentativeRoute
  field
    representedPerson : String
    agency : String
    agencyRole : String
    publicContactCarrier : String
    publicContactAddress : String
    privateContactUsed : Bool
    privateContactUsedIsFalse : privateContactUsed ≡ false

open PublicRepresentativeRoute public

ashBartyNCManagementRoute : PublicRepresentativeRoute
ashBartyNCManagementRoute =
  publicRepresentativeRoute
    "Ashleigh Barty"
    "NC Management"
    "Talent representation; contract negotiation; sponsorship; brand strategy; media/PR"
    "NC Management official website contact/client pages"
    "info@ncmanagement.com.au"
    false
    refl

------------------------------------------------------------------------
-- Triage is not consent.
------------------------------------------------------------------------

data RepresentativeTriageState : Set where
  notContacted : RepresentativeTriageState
  submittedToRepresentative : RepresentativeTriageState
  representativeRequestsInformation : RepresentativeTriageState
  representativeDeclines : RepresentativeTriageState
  representativeRoutesElsewhere : RepresentativeTriageState
  representativeAcceptsDiscussion : RepresentativeTriageState


data RepresentativeOutreachResidual : Set where
  representativeTriageUnresolved : RepresentativeOutreachResidual
  routedRecipientUnresolved : RepresentativeOutreachResidual
  participationConsentUnresolved : RepresentativeOutreachResidual
  attributionConsentUnresolved : RepresentativeOutreachResidual

record RepresentativeFirstRequest : Set where
  constructor representativeFirstRequest
  field
    route : PublicRepresentativeRoute
    factualBrief : Outreach.FactualOutreachBrief
    stewardshipBrief : Stewardship.BraidedStewardshipBrief
    requestScope : String
    asksRepresentativeToTriage : Bool
    asksRepresentativeToTriageIsTrue : asksRepresentativeToTriage ≡ true
    asksForImmediateEndorsement : Bool
    asksForImmediateEndorsementIsFalse : asksForImmediateEndorsement ≡ false
    asksForImmediatePublicity : Bool
    asksForImmediatePublicityIsFalse : asksForImmediatePublicity ≡ false

open RepresentativeFirstRequest public

currentRepresentativeFirstRequest : RepresentativeFirstRequest
currentRepresentativeFirstRequest =
  representativeFirstRequest
    ashBartyNCManagementRoute
    Outreach.currentFactualBrief
    Stewardship.currentBraidedStewardshipBrief
    "Please assess whether this private factual briefing/site-walk invitation is appropriate for Ash Barty and, if so, advise the correct representative/contact process"
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Escalation policy.
------------------------------------------------------------------------

data RepresentativeBypassWithoutReason : Set where
data AgencySubmissionAutomaticallyAshConsent : Set where
data AgencyInterestAutomaticallyPublicSupport : Set where
data FoundationContactAutomaticallyManagementApproval : Set where
data PublicistBrandFitAutomaticallyCampaignEndorsement : Set where

representativeBypassRequiresReason : RepresentativeBypassWithoutReason → ⊥
representativeBypassRequiresReason ()

agencySubmissionDoesNotAutoCreateAshConsent :
  AgencySubmissionAutomaticallyAshConsent → ⊥
agencySubmissionDoesNotAutoCreateAshConsent ()

agencyInterestDoesNotAutoCreatePublicSupport :
  AgencyInterestAutomaticallyPublicSupport → ⊥
agencyInterestDoesNotAutoCreatePublicSupport ()

foundationContactDoesNotAutoCreateManagementApproval :
  FoundationContactAutomaticallyManagementApproval → ⊥
foundationContactDoesNotAutoCreateManagementApproval ()

brandFitDoesNotAutoCreateCampaignEndorsement :
  PublicistBrandFitAutomaticallyCampaignEndorsement → ⊥
brandFitDoesNotAutoCreateCampaignEndorsement ()

------------------------------------------------------------------------
-- SOCIAL-APPROPRIATENESS / WRONGTYPE GATES
--
-- A factually justified contact can still instantiate the wrong social object.
-- These gates prevent a normal professional invitation from silently becoming
-- parasocial familiarity, moral pressure, identity leverage, sponsor leverage,
-- persistence pressure, or an over-engineered demand.
------------------------------------------------------------------------

data PublicFigureFamiliarityEqualsPersonalRelationship : Set where
data PlaygroundLegacyCreatesPersonalObligation : Set where
data IndigenousIdentityCreatesCampaignDuty : Set where
data BrandPartnerSensitivityCreatesLeverage : Set where
data NoReplyCreatesPermissionToEscalate : Set where
data FormalProofArchitectureBelongsInFirstContact : Set where
data DetailedCampaignTheoryEqualsUsefulTriageBrief : Set where
data CommunityImportanceCreatesUrgencyEntitlement : Set where

publicFamiliarityDoesNotCreatePersonalRelationship :
  PublicFigureFamiliarityEqualsPersonalRelationship → ⊥
publicFamiliarityDoesNotCreatePersonalRelationship ()

playgroundLegacyDoesNotCreatePersonalObligation :
  PlaygroundLegacyCreatesPersonalObligation → ⊥
playgroundLegacyDoesNotCreatePersonalObligation ()

indigenousIdentityDoesNotCreateCampaignDuty :
  IndigenousIdentityCreatesCampaignDuty → ⊥
indigenousIdentityDoesNotCreateCampaignDuty ()

brandSensitivityDoesNotCreateLeverage :
  BrandPartnerSensitivityCreatesLeverage → ⊥
brandSensitivityDoesNotCreateLeverage ()

noReplyDoesNotCreateEscalationPermission :
  NoReplyCreatesPermissionToEscalate → ⊥
noReplyDoesNotCreateEscalationPermission ()

formalArchitectureDoesNotBelongInFirstContact :
  FormalProofArchitectureBelongsInFirstContact → ⊥
formalArchitectureDoesNotBelongInFirstContact ()

detailedTheoryDoesNotEqualUsefulTriageBrief :
  DetailedCampaignTheoryEqualsUsefulTriageBrief → ⊥
detailedTheoryDoesNotEqualUsefulTriageBrief ()

communityImportanceDoesNotCreateUrgencyEntitlement :
  CommunityImportanceCreatesUrgencyEntitlement → ⊥
communityImportanceDoesNotCreateUrgencyEntitlement ()

record SocialAppropriatenessGate : Set where
  constructor socialAppropriatenessGate
  field
    professionalChannelUsed : Bool
    professionalChannelUsedIsTrue : professionalChannelUsed ≡ true

    firstContactShortAndTriageable : Bool
    firstContactShortAndTriageableIsTrue : firstContactShortAndTriageable ≡ true

    noParasocialFamiliarity : Bool
    noParasocialFamiliarityIsTrue : noParasocialFamiliarity ≡ true

    noPersonalObligationFraming : Bool
    noPersonalObligationFramingIsTrue : noPersonalObligationFraming ≡ true

    noIdentityLeverage : Bool
    noIdentityLeverageIsTrue : noIdentityLeverage ≡ true

    noSponsorPressure : Bool
    noSponsorPressureIsTrue : noSponsorPressure ≡ true

    noPublicPressureOnSilence : Bool
    noPublicPressureOnSilenceIsTrue : noPublicPressureOnSilence ≡ true

    noFormalismDumpInFirstContact : Bool
    noFormalismDumpInFirstContactIsTrue : noFormalismDumpInFirstContact ≡ true

    easyDeclineOrNoReplyPath : Bool
    easyDeclineOrNoReplyPathIsTrue : easyDeclineOrNoReplyPath ≡ true

canonicalSocialAppropriatenessGate : SocialAppropriatenessGate
canonicalSocialAppropriatenessGate =
  socialAppropriatenessGate
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- Preferred routing order.
------------------------------------------------------------------------

preferredInitialSurface : ContactSurface
preferredInitialSurface = authorisedManagementAgency

preferredInitialProducer : ContactProducer
preferredInitialProducer = producerForSurface preferredInitialSurface

preferredInitialProducerIsManagementTriage :
  preferredInitialProducer ≡ managementTriageProducer
preferredInitialProducerIsManagementTriage = refl

record RepresentativeFirstBoundary : Set where
  constructor representativeFirstBoundary
  field
    managementFirst : Bool
    managementFirstIsTrue : managementFirst ≡ true

    publicContactOnly : Bool
    publicContactOnlyIsTrue : publicContactOnly ≡ true

    triageEqualsConsent : Bool
    triageEqualsConsentIsFalse : triageEqualsConsent ≡ false

    brandReviewEqualsEndorsement : Bool
    brandReviewEqualsEndorsementIsFalse : brandReviewEqualsEndorsement ≡ false

    bypassAroundRepresentativeByDefault : Bool
    bypassAroundRepresentativeByDefaultIsFalse :
      bypassAroundRepresentativeByDefault ≡ false

    socialAppropriatenessChecked : Bool
    socialAppropriatenessCheckedIsTrue : socialAppropriatenessChecked ≡ true

canonicalRepresentativeFirstBoundary : RepresentativeFirstBoundary
canonicalRepresentativeFirstBoundary =
  representativeFirstBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
