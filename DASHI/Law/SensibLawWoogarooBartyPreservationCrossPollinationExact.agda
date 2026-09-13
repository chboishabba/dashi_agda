module DASHI.Law.SensibLawWoogarooBartyPreservationCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooBartyOutreachExact as Outreach
import DASHI.Law.SensibLawWoogarooBartyRepresentativeFirstOutreachExact as Representative
import DASHI.Law.SensibLawWoogarooBartyStewardshipCrossPollinationExact as Stewardship
import DASHI.Law.SensibLawWoogarooPreservationRoadmapExact as Roadmap
import DASHI.Law.SensibLawWoogarooDecisionMakerAndDelayLineageExact as Decision
import DASHI.Law.SensibLawWoogarooPoliticalAlignmentExact as Politics

------------------------------------------------------------------------
-- ASH BARTY / WOOGAROO PRESERVATION CROSS-POLLINATION
--
-- The preservation lane may strengthen the factual reason for outreach and
-- provide a real decision window.  It must not convert local connection,
-- urgency, celebrity, Indigenous identity, sponsorship, or public profile into
-- an obligation, endorsement, custodial authority, or statutory decision role.
------------------------------------------------------------------------

data OutreachPreservationCoordinate : Set where
  localPlaceNexus : OutreachPreservationCoordinate
  activeFederalDecisionWindow : OutreachPreservationCoordinate
  threatenedSpeciesAndHabitat : OutreachPreservationCoordinate
  privateSiteWalkOrBriefing : OutreachPreservationCoordinate
  representativeTriage : OutreachPreservationCoordinate
  publicAttributionConsent : OutreachPreservationCoordinate

data PublicFacingUrgency : Set where
  boundedActiveDecisionWindow : PublicFacingUrgency

record PreservationAwareOutreachBrief : Set where
  constructor preservation-aware-outreach-brief
  field
    baseBrief : Outreach.FactualOutreachBrief
    representativeRequest : Representative.RepresentativeFirstRequest
    stewardshipBrief : Stewardship.BraidedStewardshipBrief
    activeFederalDecision : Roadmap.RoadmapCoordinate
    factualReasonForTiming : String
    privateBriefingDefault : Bool
    privateBriefingDefaultIsTrue : privateBriefingDefault ≡ true
    asksForImmediateEndorsement : Bool
    asksForImmediateEndorsementIsFalse : asksForImmediateEndorsement ≡ false
    usesDeadlineAsPressure : Bool
    usesDeadlineAsPressureIsFalse : usesDeadlineAsPressure ≡ false
    attributesCustodialAuthorityToAsh : Bool
    attributesCustodialAuthorityToAshIsFalse : attributesCustodialAuthorityToAsh ≡ false

open PreservationAwareOutreachBrief public

currentPreservationAwareBartyBrief : PreservationAwareOutreachBrief
currentPreservationAwareBartyBrief = preservation-aware-outreach-brief
  Outreach.currentFactualBrief
  Representative.currentRepresentativeFirstRequest
  Stewardship.currentBraidedStewardshipBrief
  Roadmap.federal8575
  "There is an active Commonwealth EPBC decision window for Springfield Residential Development (EPBC 2019/8575), with the current decision deadline source-paid as 1 October 2026. This may make a timely private factual briefing useful, but does not create any personal obligation to participate."
  true refl
  false refl
  false refl
  false refl

------------------------------------------------------------------------
-- Urgency is internal strategy, not interpersonal entitlement.
------------------------------------------------------------------------

data StatutoryDeadlineCreatesCelebrityObligation : Set where
data LocalNexusCreatesCampaignDuty : Set where
data SiteWalkConsentCreatesPublicEndorsement : Set where
data PrivateBriefingCreatesPoliticalAuthority : Set where
data PublicProfileCreatesStatutoryInfluenceRight : Set where

statutoryDeadlineDoesNotCreateCelebrityObligation :
  StatutoryDeadlineCreatesCelebrityObligation → ⊥
statutoryDeadlineDoesNotCreateCelebrityObligation ()

localNexusDoesNotCreateCampaignDuty : LocalNexusCreatesCampaignDuty → ⊥
localNexusDoesNotCreateCampaignDuty ()

siteWalkConsentDoesNotCreatePublicEndorsement : SiteWalkConsentCreatesPublicEndorsement → ⊥
siteWalkConsentDoesNotCreatePublicEndorsement ()

privateBriefingDoesNotCreatePoliticalAuthority : PrivateBriefingCreatesPoliticalAuthority → ⊥
privateBriefingDoesNotCreatePoliticalAuthority ()

publicProfileDoesNotCreateStatutoryInfluenceRight : PublicProfileCreatesStatutoryInfluenceRight → ⊥
publicProfileDoesNotCreateStatutoryInfluenceRight ()

------------------------------------------------------------------------
-- Public-facing compression rule.
--
-- Internally we retain the exact 1 October deadline, delegate, party/political
-- routing and preservation cutset.  The first representative contact should
-- compress that to the bounded fact that there is an active federal decision
-- window, unless management asks for the detailed decision chronology.
------------------------------------------------------------------------

record OutreachCompressionBoundary : Set where
  constructor outreach-compression-boundary
  field
    exactDeadlineRetainedInternally : Bool
    exactDeadlineRetainedInternallyIsTrue : exactDeadlineRetainedInternally ≡ true
    firstContactNeedsFullLegalArchitecture : Bool
    firstContactNeedsFullLegalArchitectureIsFalse :
      firstContactNeedsFullLegalArchitecture ≡ false
    firstContactMayStateActiveDecisionWindow : Bool
    firstContactMayStateActiveDecisionWindowIsTrue :
      firstContactMayStateActiveDecisionWindow ≡ true
    politicalPartyGraphBelongsInFirstContact : Bool
    politicalPartyGraphBelongsInFirstContactIsFalse :
      politicalPartyGraphBelongsInFirstContact ≡ false

canonicalOutreachCompressionBoundary : OutreachCompressionBoundary
canonicalOutreachCompressionBoundary =
  outreach-compression-boundary
    true refl
    false refl
    true refl
    false refl

------------------------------------------------------------------------
-- Surrounding-content braid.
--
-- Preservation evidence, political advocacy and public-figure outreach are
-- parallel consumers.  None may consume the authority of another.
------------------------------------------------------------------------

record WoogarooSurroundingContentBraid : Set where
  constructor woogaroo-surrounding-content-braid
  field
    preservationRoadmap : Roadmap.HighestAlphaPath
    representativeRoute : Representative.PublicRepresentativeRoute
    stewardshipBoundary : Stewardship.WoogarooBraidedStewardshipBoundary
    federalDelegate : Decision.PoliticalRoleReceipt
    federalPortfolioRoute : Politics.PoliticalAlignmentReceipt
    preservesIndependentConsumers : Bool
    preservesIndependentConsumersIsTrue : preservesIndependentConsumers ≡ true

open WoogarooSurroundingContentBraid public

canonicalWoogarooSurroundingContentBraid : WoogarooSurroundingContentBraid
canonicalWoogarooSurroundingContentBraid = woogaroo-surrounding-content-braid
  Roadmap.currentHighestAlphaPath
  Representative.ashBartyNCManagementRoute
  Stewardship.canonicalWoogarooBraidedStewardshipBoundary
  Decision.declanOConnorCoxEPBC8575DelegateReceipt
  Politics.murrayWattAlignment
  true refl
