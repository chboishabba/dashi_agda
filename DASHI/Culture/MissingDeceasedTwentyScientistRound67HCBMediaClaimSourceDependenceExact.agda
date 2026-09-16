module DASHI.Culture.MissingDeceasedTwentyScientistRound67HCBMediaClaimSourceDependenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Culture.MissingDeceasedTwentyScientistRound48AntiEchoChamberMethodologyExact as AntiEcho
import DASHI.Culture.MissingDeceasedTwentyScientistRound66HCBTemporalInstitutionalOverlapExact as R66

------------------------------------------------------------------------
-- ROUND 67: HCB MEDIA-CLAIM SOURCE-DEPENDENCE AUDIT
--
-- Several 2026 secondary/podcast/blog surfaces repeat stronger propositions:
-- McCasland directly funded, oversaw, supervised, or personally worked with
-- Monica Jacinto/Reza's Mondaloy/HCB activity.  Current primary acquisition
-- pays only a narrower chain:
--
--   McCasland commanded AFRL May 2011-Jul 2013
--   + exact HCB programme/contract active under AFRL in Aug-Sep 2012
--   + AFRL's public 2011 Technology Milestones book places propulsion,
--     liquid rockets, rocket materials and related materials work inside the
--     laboratory portfolio under McCasland's command.
--
-- It does not name McCasland on HCB/Mondaloy or a Reza task/review/funding
-- decision.  Repetition of the stronger derivative claim therefore cannot
-- multiply primary support.
------------------------------------------------------------------------

record MediaClaimFamily : Set where
  constructor media-claim-family
  field
    familyLabel : String
    claimReference : String
    sourceRoleReference : String
    primaryIdentityBearingCarrierLocated : Bool
    paysDirectFundingOrSupervision : Bool

open MediaClaimFamily public

worldOfStrangeClaim : MediaClaimFamily
worldOfStrangeClaim = media-claim-family
  "World Of The Strange / derivative web narrative"
  "Reza research directly funded by military programmes overseen by McCasland"
  "secondary narrative; useful as a lead only"
  false false

podcastFundingClaim : MediaClaimFamily
podcastFundingClaim = media-claim-family
  "Dreamland / podcast mirrors"
  "McCasland budget directly funded programmes depending on Reza alloy"
  "secondary podcast narrative; useful as a lead only"
  false false

podcastOversightClaim : MediaClaimFamily
podcastOversightClaim = media-claim-family
  "All Things Unexplained / podcast transcript"
  "McCasland oversaw AFRL during Mondaloy development and therefore had a role"
  "secondary interpretive narrative; institutional premise partly primary-paid, personal inference unpaid"
  false false

mediaClaimFamilyCount : Nat
mediaClaimFamilyCount = 3

------------------------------------------------------------------------
-- Primary source family.
------------------------------------------------------------------------

afrlTechnologyMilestones2011 : Attribution.AttributedSource
afrlTechnologyMilestones2011 = Attribution.mkNoDOISource
  "Air Force Research Laboratory"
  "AFRL Technology Milestones Program: 2011 Technology Milestones"
  "Wright-Patterson AFB public-release technical programme book; 88ABW-2012-5343"
  "2012"
  "https://www.wpafb.af.mil/shared/media/document/AFD-121001-034.pdf"
  Attribution.governmentSource
  "Pays McCasland's commander attribution on the public AFRL portfolio carrier and shows propulsion/liquid-rockets/rocket-materials programme families within AFRL; does not name HCB, Mondaloy, Monica Jacinto/Reza, or a McCasland task-level decision on those objects."
  Attribution.publicAttribution

mccaslandBiography : Attribution.AttributedSource
mccaslandBiography = R66.mccaslandOfficialBiography

hcbIndustryDay : Attribution.AttributedSource
hcbIndustryDay = R66.hcbIndustryDayNotice

------------------------------------------------------------------------
-- Paid / unpaid coordinates.
------------------------------------------------------------------------

afrlCommandAndPortfolioPaid : Bool
afrlCommandAndPortfolioPaid = true

hcbExactProgrammeActivePaid : Bool
hcbExactProgrammeActivePaid = true

milestonesBookNamesMcCaslandAsCommanderPaid : Bool
milestonesBookNamesMcCaslandAsCommanderPaid = true

milestonesBookShowsPropulsionAndRocketMaterialsPortfolioPaid : Bool
milestonesBookShowsPropulsionAndRocketMaterialsPortfolioPaid = true

milestonesBookNamesMondaloyOrHCBPaid : Bool
milestonesBookNamesMondaloyOrHCBPaid = false

milestonesBookNamesRezaPaid : Bool
milestonesBookNamesRezaPaid = false

directFundingOrSupervisionPrimaryPaid : Bool
directFundingOrSupervisionPrimaryPaid = false

personalHCBTaskRolePrimaryPaid : Bool
personalHCBTaskRolePrimaryPaid = false

personalMondaloyReviewOrFundingDecisionPaid : Bool
personalMondaloyReviewOrFundingDecisionPaid = false

------------------------------------------------------------------------
-- Anti-echo / attribution firewalls.
------------------------------------------------------------------------

mediaRepetitionDoesNotMultiplyPrimarySupport : Bool
mediaRepetitionDoesNotMultiplyPrimarySupport = AntiEcho.agreementAcrossDependentCopiesDoesNotMultiplyEvidence

commanderBudgetAuthorityDoesNotPayTaskLevelFundingDecision : Bool
commanderBudgetAuthorityDoesNotPayTaskLevelFundingDecision = true

portfolioScopeDoesNotPayNamedTaskParticipation : Bool
portfolioScopeDoesNotPayNamedTaskParticipation = true

secondaryInferenceCannotUpgradePrimaryPropositionScope : Bool
secondaryInferenceCannotUpgradePrimaryPropositionScope = true

boundedPrimarySearchNoHitDoesNotPayUniversalAbsence : Bool
boundedPrimarySearchNoHitDoesNotPayUniversalAbsence = true

noPrimaryHitDoesNotMeanMediaClaimFalse : Bool
noPrimaryHitDoesNotMeanMediaClaimFalse = true

noPrimaryHitLeavesClaimUnpaid : Bool
noPrimaryHitLeavesClaimUnpaid = true

------------------------------------------------------------------------
-- Scheduler consequence.
------------------------------------------------------------------------

hcbBranchStillLive : Bool
hcbBranchStillLive = true

nextIdentityBearingCarrier : String
nextIdentityBearingCarrier = "Acquire an identity-bearing FA9300-07-C-0001 / HBTD / Mondaloy task, review, funding, roster or contract-management carrier naming McCasland; derivative narratives and organisation-level portfolio documents are now dominated unless they expose such a primary locator."

round67H2PaidCount : Nat
round67H2PaidCount = 0

round67H3PaidCount : Nat
round67H3PaidCount = 0

round67Reading : String
round67Reading = "The stronger 2026 McCasland-Reza funding/supervision narratives remain derivative. Primary government records pay that McCasland commanded AFRL during active HCB work and that AFRL's public portfolio included propulsion, liquid rockets and rocket materials, but the acquired primary surfaces do not name McCasland on HCB, Mondaloy, Monica Jacinto/Reza, or a task-level funding/review decision. Repeated secondary claims therefore do not multiply primary evidence. The exact HCB branch remains live only for an identity-bearing task/review/funding/roster carrier; absence from the bounded searched surfaces is not a universal non-participation claim."
