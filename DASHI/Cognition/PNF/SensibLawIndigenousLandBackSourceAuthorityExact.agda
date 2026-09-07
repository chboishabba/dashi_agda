module DASHI.Cognition.PNF.SensibLawIndigenousLandBackSourceAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Source-attribution constitution for the global LAND BACK evidence lane.
--
-- The repository-wide attribution rule has not changed.  This owner makes the
-- standing rule explicit for this lane: source authorship, underlying-data
-- provenance, publication status, evidential design, causal permission and our
-- later interpretation are distinct coordinates.
------------------------------------------------------------------------

data SourceAuthorityKind : Set where
  peerReviewedCausalStudy : SourceAuthorityKind
  peerReviewedComparativeStudy : SourceAuthorityKind
  peerReviewedSystematicReview : SourceAuthorityKind
  officialAdministrativeReceipt : SourceAuthorityKind
  officialAdministrativePolicy : SourceAuthorityKind
  governmentResearchCommunication : SourceAuthorityKind
  independentPolicyResearch : SourceAuthorityKind
  academicDescriptiveStatisticalSynthesis : SourceAuthorityKind
  economicValuationReport : SourceAuthorityKind
  historicalPolicyAnalysis : SourceAuthorityKind
  workingPaperCausalClaim : SourceAuthorityKind
  commercialMarketObservation : SourceAuthorityKind
  criticalInterpretation : SourceAuthorityKind
  normativeDecolonialHypothesis : SourceAuthorityKind


data PublicationStatus : Set where
  peerReviewedPublished : PublicationStatus
  officialPublished : PublicationStatus
  institutionalReportPublished : PublicationStatus
  workingPaperNotPeerReviewed : PublicationStatus
  commercialObservationPublished : PublicationStatus
  interpretiveLayerOnly : PublicationStatus


record SourceAuthorityReceipt : Set where
  constructor sourceAuthorityReceipt
  field
    sourceId : String
    citation : String
    year : Nat
    authorityKind : SourceAuthorityKind
    publicationStatus : PublicationStatus
    directClaimBoundary : String
    peerReviewed : Bool
    analysisAuthorIsGovernment : Bool
    usesOfficialUnderlyingData : Bool
    causalClaimAllowed : Bool
    universalGeneralisationAllowed : Bool
    universalGeneralisationAllowedIsFalse : universalGeneralisationAllowed ≡ false
    sourceAttributionRequired : Bool
    sourceAttributionRequiredIsTrue : sourceAttributionRequired ≡ true
open SourceAuthorityReceipt public

-- 2024 Brazilian Legal Amazon competing-land-use comparison.
denBraber2024Authority : SourceAuthorityReceipt
denBraber2024Authority = sourceAuthorityReceipt
  "den-braber-2024-amazon-tradeoffs"
  "den Braber et al., Nature Ecology & Evolution 8 (2024) 1482-1492, doi:10.1038/s41559-024-02458-w"
  2024
  peerReviewedComparativeStudy
  peerReviewedPublished
  "peer-reviewed comparative study of deforestation and selected socioeconomic indicators across protected-area/Indigenous-territory treatments and competing land-use controls in the Brazilian Legal Amazon; study design and reported estimates remain source-owned"
  true false true false false refl true refl

-- U.S. land-back economic study: causal methods claimed, but still an SSRN working paper.
arcoiteJohnson2025Authority : SourceAuthorityReceipt
arcoiteJohnson2025Authority = sourceAuthorityReceipt
  "arcoite-johnson-2025-landback-working-paper"
  "Arcoite & Johnson, Land-Back to Move Forward?, SSRN 5189600, posted 28 Apr 2025"
  2025
  workingPaperCausalClaim
  workingPaperNotPeerReviewed
  "authors report IV/endogenous-treatment estimates across more than 1,700 Indigenous communities; working-paper authorship and non-peer-reviewed status remain visible"
  false false false true false refl true refl

-- U.S. Department of the Interior program totals are administrative facts, not outcome estimates.
doiLandBuyBackAuthority : SourceAuthorityReceipt
doiLandBuyBackAuthority = sourceAuthorityReceipt
  "doi-land-buyback-program-conclusion"
  "U.S. Department of the Interior, Land Buy-Back Program for Tribal Nations conclusion / program history"
  2023
  officialAdministrativeReceipt
  officialPublished
  "official program totals concerning acreage returned to Tribal trust ownership and payments to participating landowners; no causal socioeconomic effect inferred from administrative totals alone"
  false true true false false refl true refl

-- WRI valuation is an institutional economic valuation, not a causal experiment.
wriTenureEconomicValuationAuthority : SourceAuthorityReceipt
wriTenureEconomicValuationAuthority = sourceAuthorityReceipt
  "wri-2016-climate-benefits-tenure-costs"
  "WRI, Climate Benefits, Tenure Costs / Protecting Indigenous Land Rights Makes Good Economic Sense (2016)"
  2016
  economicValuationReport
  institutionalReportPublished
  "WRI economic valuation of tenure-secure Indigenous/community forests in Bolivia, Brazil and Colombia; valuation estimates do not become causal land-return effects"
  false false false false false refl true refl

-- CPI/PUC-Rio is independent policy research using official Brazilian datasets.
-- The analysis is NOT itself an official-government proposition.
cpi2024RuralCreditAuthority : SourceAuthorityReceipt
cpi2024RuralCreditAuthority = sourceAuthorityReceipt
  "cpi-2024-rural-credit-deforestation"
  "Climate Policy Initiative / PUC-Rio, Credit Where It's Due: Rural Credit Subsidies and Deforestation (2024)"
  2024
  independentPolicyResearch
  institutionalReportPublished
  "independent CPI/PUC-Rio analysis joining official SICOR/BCB, SICAR and PRODES data; its reported association between subsidized rural credit and properties with deforestation remains CPI/PUC-Rio's analytical proposition, not a Brazilian-government holding"
  false false true false false refl true refl

-- Historical policy distortion literature is retained as historical, not projected into every current case.
binswanger1991Authority : SourceAuthorityReceipt
binswanger1991Authority = sourceAuthorityReceipt
  "binswanger-1991-brazil-policy-deforestation"
  "Binswanger, Brazilian policies that encourage deforestation in the Amazon, World Development 19(7) (1991) 821-829"
  1991
  historicalPolicyAnalysis
  peerReviewedPublished
  "historical peer-reviewed analysis of tax, land-allocation, tax-credit and subsidized-credit incentives; temporal scope is not silently promoted to current universal mechanism"
  true false false false false refl true refl

margulis2003Authority : SourceAuthorityReceipt
margulis2003Authority = sourceAuthorityReceipt
  "margulis-2003-causes-amazon-deforestation"
  "Sergio Margulis, Causes of Deforestation of the Brazilian Amazon, World Bank Working Paper 22 / report 27715"
  2003
  historicalPolicyAnalysis
  institutionalReportPublished
  "World Bank-authored analytical report on deforestation drivers and private/social returns; institutional publication does not make its analytical propositions government adjudications or present-day universal mechanisms"
  false false false false false refl true refl

-- Harvard Ash Center databook: academic synthesis of official Census/ACS data.
ashCenter2025DatabookAuthority : SourceAuthorityReceipt
ashCenter2025DatabookAuthority = sourceAuthorityReceipt
  "ash-center-2025-reservation-databook"
  "Medford & Akee, Social and Economic Changes in American Indian Reservations, Third Edition 1990-2020, Harvard Ash Center (2025)"
  2025
  academicDescriptiveStatisticalSynthesis
  institutionalReportPublished
  "Harvard academic/institutional synthesis of U.S. Census and ACS statistics; trends are descriptive and remain the authors' compilation, not an official administrative outcome receipt or land-return causal estimate"
  false false true false false refl true refl

-- BIA carbon policy is an official administrative-policy interpretation.
biaCarbon2023Authority : SourceAuthorityReceipt
biaCarbon2023Authority = sourceAuthorityReceipt
  "bia-npm-trus-47-a1-carbon-policy"
  "U.S. Bureau of Indian Affairs NPM-TRUS-47 A1, Carbon Sequestration Agreement Policy - Amendment 1 (31 Oct 2023)"
  2023
  officialAdministrativePolicy
  officialPublished
  "BIA policy states that carbon is not considered a trust asset because it is neither harvested nor extracted as a forest/agricultural product and its value derives from storage capacity; this is an agency policy interpretation, not a general theorem about stewardship value"
  false true true false false refl true refl

-- Abatable supplies proprietary/commercial voluntary-carbon-market observations.
abatable2025ReddPriceAuthority : SourceAuthorityReceipt
abatable2025ReddPriceAuthority = sourceAuthorityReceipt
  "abatable-2025-brazil-redd-price"
  "Abatable, The new floor price for REDD+ carbon credits (2025; pricing dataset as of Q1 2025)"
  2025
  commercialMarketObservation
  commercialObservationPublished
  "commercial carbon-market analysis reports a median Brazil REDD+ spot price of USD 2.50/unit at end-Q1 2025 and models substantially higher prices needed for new high-integrity methodologies; market observation is not a public-law or welfare valuation proposition"
  false false false false false refl true refl

-- Embrapa communication reports results of a Poyanawa carbon-credit study.
embrapaPoyanawa2021Authority : SourceAuthorityReceipt
embrapaPoyanawa2021Authority = sourceAuthorityReceipt
  "embrapa-poyanawa-carbon-2021"
  "Embrapa, Study reveals Indigenous Land's potential to generate carbon credits (2021)"
  2021
  governmentResearchCommunication
  officialPublished
  "government research communication reports estimated avoided emissions and illustrative carbon-credit revenue for the Poyanawa Indigenous Land; communication/reporting status is distinct from peer-reviewed causal evidence"
  false true false false false refl true refl

-- Vasco et al. directly compare land-use patterns; the authors caution that the
-- cross-sectional multivariate estimates are not causal effects.
vasco2018LandUseAuthority : SourceAuthorityReceipt
vasco2018LandUseAuthority = sourceAuthorityReceipt
  "vasco-2018-ecuador-amazon-land-use"
  "Vasco et al., Agricultural land use among mestizo colonist and indigenous populations: Contrasting patterns in the Amazon, PLoS ONE 13(7):e0199518 (2018)"
  2018
  peerReviewedComparativeStudy
  peerReviewedPublished
  "peer-reviewed household-survey comparison of colonist, Kichwa and Shuar land-use patterns in Pastaza; authors explicitly state the cross-sectional results cannot be interpreted as causal effects"
  true false false false false refl true refl

------------------------------------------------------------------------
-- Source-proposition firewalls.
------------------------------------------------------------------------

data WorkingPaperEqualsPeerReviewedResult : Set where
data AdministrativeAcreageEqualsEconomicOutcome : Set where
data EconomicValuationEqualsCausalEffect : Set where
data SubsidizedCreditAssociationExplainsAllIncomeDifference : Set where
data HistoricalSubsidyMechanismEqualsCurrentUniversalMechanism : Set where
data ComparativeIncomeResultProvesGovernanceDeficiency : Set where
data OfficialUnderlyingDataMakesDerivedAnalysisOfficial : Set where
data AcademicDatabookEqualsOfficialAdministrativeReceipt : Set where
data CommercialMarketPriceEqualsSocialValue : Set where
data AgencyPolicyClassificationExhaustsStewardshipValue : Set where

workingPaperDoesNotEqualPeerReview : WorkingPaperEqualsPeerReviewedResult → ⊥
workingPaperDoesNotEqualPeerReview ()
acreageDoesNotEqualEconomicOutcome : AdministrativeAcreageEqualsEconomicOutcome → ⊥
acreageDoesNotEqualEconomicOutcome ()
valuationDoesNotEqualCausalEffect : EconomicValuationEqualsCausalEffect → ⊥
valuationDoesNotEqualCausalEffect ()
creditAssociationDoesNotExplainAllIncomeDifference : SubsidizedCreditAssociationExplainsAllIncomeDifference → ⊥
creditAssociationDoesNotExplainAllIncomeDifference ()
historicalMechanismDoesNotAutoGeneralise : HistoricalSubsidyMechanismEqualsCurrentUniversalMechanism → ⊥
historicalMechanismDoesNotAutoGeneralise ()
incomeResultDoesNotProveGovernanceDeficiency : ComparativeIncomeResultProvesGovernanceDeficiency → ⊥
incomeResultDoesNotProveGovernanceDeficiency ()
officialInputDoesNotTransferAuthorship : OfficialUnderlyingDataMakesDerivedAnalysisOfficial → ⊥
officialInputDoesNotTransferAuthorship ()
academicDatabookDoesNotBecomeAdministrativeReceipt : AcademicDatabookEqualsOfficialAdministrativeReceipt → ⊥
academicDatabookDoesNotBecomeAdministrativeReceipt ()
marketPriceDoesNotEqualSocialValue : CommercialMarketPriceEqualsSocialValue → ⊥
marketPriceDoesNotEqualSocialValue ()
agencyCategoryDoesNotExhaustStewardshipValue : AgencyPolicyClassificationExhaustsStewardshipValue → ⊥
agencyCategoryDoesNotExhaustStewardshipValue ()
