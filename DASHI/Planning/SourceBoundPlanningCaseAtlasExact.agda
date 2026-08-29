module DASHI.Planning.SourceBoundPlanningCaseAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Governance.BritishColumbiaDecriminalizationBundleExact as BC
import DASHI.Governance.ComparativeCrisisClimateAtlas as Crisis

------------------------------------------------------------------------
-- SOURCE-BOUND PLANNING CASE ATLAS
--
-- Stable historical/legal source anchors and live-refresh boundaries only.
-- Generic theorems live elsewhere; case labels never create factual, legal or
-- political authority by themselves.
------------------------------------------------------------------------

data PlanningCase : Set where
  juukanGorgeCase voiceTreatyTruthCase deathsInCustodyCase
  britishColumbiaCase trumpIranPalestineCase goldCoastPlanningCase : PlanningCase

data SourceFreshness : Set where
  stableHistoricalAnchor liveRefreshRequired : SourceFreshness

record CaseSource : Set where
  constructor caseSource
  field
    case : PlanningCase
    institutionOrAuthor : String
    title : String
    sourceDateOrYear : String
    importedRole : String
    freshness : SourceFreshness
    createsLegalConclusion : Bool
    createsPoliticalAuthority : Bool

open CaseSource public

juukanInquirySource : CaseSource
juukanInquirySource = caseSource juukanGorgeCase
  "Parliament of Australia"
  "A Way Forward: Final report into the destruction of Indigenous heritage sites at Juukan Gorge"
  "2021"
  "source anchor for legal permission, new evidence, bargaining-power and heritage-protection failure analysis"
  stableHistoricalAnchor false false

voiceReferendumSource : CaseSource
voiceReferendumSource = caseSource voiceTreatyTruthCase
  "Australian Electoral Commission"
  "2023 referendum national results"
  "2023"
  "source anchor for the referendum result; does not settle sovereignty"
  stableHistoricalAnchor false false

deathsInCustodySource : CaseSource
deathsInCustodySource = caseSource deathsInCustodyCase
  "Royal Commission into Aboriginal Deaths in Custody"
  "National Report"
  "1991"
  "source anchor for inquiry/recommendation versus implementation distinctions"
  stableHistoricalAnchor false false

trumpIranPalestineLiveSourceBoundary : CaseSource
trumpIranPalestineLiveSourceBoundary = caseSource trumpIranPalestineCase
  "external current-source bundle required"
  "Trump / Iran / Israel-Palestine live policy and conflict corpus"
  "2026-current"
  "must be refreshed before any current factual comparison or PNF receipt campaign"
  liveRefreshRequired false false

goldCoastLivePlanningBoundary : CaseSource
goldCoastLivePlanningBoundary = caseSource goldCoastPlanningCase
  "external current-source bundle required"
  "Gold Coast / Queensland transport, density and planning corpus"
  "2026-current"
  "must be refreshed before factual use; branding, technology, approval and social legitimacy remain distinct"
  liveRefreshRequired false false

-- Existing source-native owners remain authoritative for their domains.
bcSourceOwner : BC.InterventionBundle
bcSourceOwner = BC.initialPilotBundle

comparativeCrisisOwner : Crisis.ComparativeCrisisClimateAtlasSurface
comparativeCrisisOwner = Crisis.canonicalComparativeCrisisClimateAtlasSurface

record CaseAtlasBoundary : Set where
  constructor caseAtlasBoundary
  field
    juukanCreatesUniversalMiningTheorem : Bool
    juukanCreatesUniversalMiningTheoremIsFalse : juukanCreatesUniversalMiningTheorem ≡ false
    referendumResultSettlesSovereignty : Bool
    referendumResultSettlesSovereigntyIsFalse : referendumResultSettlesSovereignty ≡ false
    inquiryRecommendationEqualsImplementation : Bool
    inquiryRecommendationEqualsImplementationIsFalse :
      inquiryRecommendationEqualsImplementation ≡ false
    staleLiveCaseMayBeTreatedAsCurrent : Bool
    staleLiveCaseMayBeTreatedAsCurrentIsFalse : staleLiveCaseMayBeTreatedAsCurrent ≡ false

canonicalCaseAtlasBoundary : CaseAtlasBoundary
canonicalCaseAtlasBoundary = caseAtlasBoundary false refl false refl false refl false refl
