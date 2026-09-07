module DASHI.Cognition.PNF.SensibLawIndigenousLandBackSocioeconomicModeratorHyperfabricExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawIndigenousLandBackGlobalEvidenceExact as Atlas
import DASHI.Cognition.PNF.SensibLawIndigenousLandBackSourceAuthorityExact as Authority

------------------------------------------------------------------------
-- Socioeconomic moderator hyperfabric.
--
-- The 2024 Brazilian Legal Amazon study's selected socioeconomic indicators
-- are decomposed rather than collapsed into one `mixed trade-off` scalar.
-- Externality/subsidy/market-integration hypotheses are kept separate from
-- peer-reviewed outcome receipts.
------------------------------------------------------------------------

data SocioeconomicIndicator : Set where
  meanMonthlyHouseholdIncome : SocioeconomicIndicator
  householdIncomeInequalityGini : SocioeconomicIndicator
  literacyRate : SocioeconomicIndicator
  poorSanitationShare : SocioeconomicIndicator
  lowIncomePopulationShare : SocioeconomicIndicator
  unemploymentRate : SocioeconomicIndicator


data ObservedDirection : Set where
  significantlyHigher : ObservedDirection
  significantlyLower : ObservedDirection
  noConsistentSignificantDifference : ObservedDirection
  comparatorDependent : ObservedDirection
  notObservedInStudy : ObservedDirection


data ComparatorKind : Set where
  sparselyPopulatedControl : ComparatorKind
  verySmallAgriculturalLandholders : ComparatorKind
  smallAgriculturalLandholders : ComparatorKind
  mediumAgriculturalLandholders : ComparatorKind
  largeAgriculturalLandholders : ComparatorKind
  legalMiningConcessions : ComparatorKind
  usIndigenousCommunityPanel : ComparatorKind


record DisaggregatedOutcomeReceipt : Set where
  constructor disaggregatedOutcomeReceipt
  field
    source : Authority.SourceAuthorityReceipt
    indicator : SocioeconomicIndicator
    comparator : ComparatorKind
    direction : ObservedDirection
    effectBasisPointsOrSentinel : Nat
    exactMagnitudeEncoded : Bool
    peerReviewedOutcome : Bool
    sourceSummary : String
open DisaggregatedOutcomeReceipt public

-- den Braber et al. 2024: IT income changes were smaller against some controls.
denBraberIncomeVsSparse : DisaggregatedOutcomeReceipt
denBraberIncomeVsSparse = disaggregatedOutcomeReceipt
  Authority.denBraber2024Authority
  meanMonthlyHouseholdIncome
  sparselyPopulatedControl
  significantlyLower
  3220
  true
  true
  "Indigenous territories linked to 32.2% smaller increases in mean household income relative to sparsely populated controls"

denBraberIncomeVsVerySmall : DisaggregatedOutcomeReceipt
denBraberIncomeVsVerySmall = disaggregatedOutcomeReceipt
  Authority.denBraber2024Authority
  meanMonthlyHouseholdIncome
  verySmallAgriculturalLandholders
  significantlyLower
  3580
  true
  true
  "Indigenous territories linked to 35.8% smaller increases in mean household income relative to very-small-landholder controls"

denBraberIncomeVsLarge : DisaggregatedOutcomeReceipt
denBraberIncomeVsLarge = disaggregatedOutcomeReceipt
  Authority.denBraber2024Authority
  meanMonthlyHouseholdIncome
  largeAgriculturalLandholders
  significantlyLower
  2960
  true
  true
  "Indigenous territories linked to 29.6% smaller increases in mean household income relative to large-landholder controls"

-- The same paper reports lower inequality against very-small and small controls.
denBraberGiniVsVerySmall : DisaggregatedOutcomeReceipt
denBraberGiniVsVerySmall = disaggregatedOutcomeReceipt
  Authority.denBraber2024Authority
  householdIncomeInequalityGini
  verySmallAgriculturalLandholders
  significantlyLower
  2140
  true
  true
  "Indigenous territories associated with 21.4% lower income inequality relative to very-small-landholder controls"

denBraberGiniVsSmall : DisaggregatedOutcomeReceipt
denBraberGiniVsSmall = disaggregatedOutcomeReceipt
  Authority.denBraber2024Authority
  householdIncomeInequalityGini
  smallAgriculturalLandholders
  significantlyLower
  1430
  true
  true
  "Indigenous territories associated with 14.3% lower income inequality relative to small-landholder controls"

-- Literacy/sanitation do not support a single uniform Indigenous-territory penalty.
denBraberLiteracySurface : DisaggregatedOutcomeReceipt
denBraberLiteracySurface = disaggregatedOutcomeReceipt
  Authority.denBraber2024Authority
  literacyRate
  sparselyPopulatedControl
  noConsistentSignificantDifference
  0
  false
  true
  "No uniform Indigenous-territory literacy penalty is established across the main competing-land-use comparisons"

denBraberSanitationSurface : DisaggregatedOutcomeReceipt
denBraberSanitationSurface = disaggregatedOutcomeReceipt
  Authority.denBraber2024Authority
  poorSanitationShare
  sparselyPopulatedControl
  noConsistentSignificantDifference
  0
  false
  true
  "No uniform Indigenous-territory sanitation penalty is established across the main competing-land-use comparisons"

------------------------------------------------------------------------
-- U.S. land-back working-paper lane remains separate and source-ranked.
------------------------------------------------------------------------

arcoiteJohnsonLowIncome : DisaggregatedOutcomeReceipt
arcoiteJohnsonLowIncome = disaggregatedOutcomeReceipt
  Authority.arcoiteJohnson2025Authority
  lowIncomePopulationShare
  usIndigenousCommunityPanel
  significantlyLower
  0
  false
  false
  "Working paper reports reductions in percentage of citizens living on low incomes using panel IV/endogenous-treatment methods; exact effect magnitude is not promoted here"

arcoiteJohnsonUnemployment : DisaggregatedOutcomeReceipt
arcoiteJohnsonUnemployment = disaggregatedOutcomeReceipt
  Authority.arcoiteJohnson2025Authority
  unemploymentRate
  usIndigenousCommunityPanel
  significantlyLower
  0
  false
  false
  "Working paper reports reductions in unemployment using panel IV/endogenous-treatment methods; working-paper status remains explicit"

------------------------------------------------------------------------
-- Market/subsidy/externality moderators.
------------------------------------------------------------------------

data ModeratorKind : Set where
  subsidizedRuralCreditExposure : ModeratorKind
  historicalTaxCreditDistortion : ModeratorKind
  landClearingAsTenureSignal : ModeratorKind
  extractiveCommodityProfitability : ModeratorKind
  ecosystemServiceExternality : ModeratorKind
  transferAccessConstraint : ModeratorKind
  marketIntegrationIntensity : ModeratorKind
  indigenousDecisionAuthorityModerator : ModeratorKind
  collectiveTenureSecurityModerator : ModeratorKind
  territorialControlModerator : ModeratorKind


data ModeratorEvidenceStatus : Set where
  officialAssociationMapped : ModeratorEvidenceStatus
  historicalMechanismMapped : ModeratorEvidenceStatus
  economicValuationMapped : ModeratorEvidenceStatus
  sourceSuggestedMechanism : ModeratorEvidenceStatus
  criticalHypothesisOnly : ModeratorEvidenceStatus


record SocioeconomicModeratorReceipt : Set where
  constructor socioeconomicModeratorReceipt
  field
    moderator : ModeratorKind
    source : Authority.SourceAuthorityReceipt
    status : ModeratorEvidenceStatus
    appliesDirectlyToDenBraberTreatmentContrast : Bool
    directCausalContributionToIncomeDifferenceProved : Bool
    directCausalContributionToIncomeDifferenceProvedIsFalse : directCausalContributionToIncomeDifferenceProved ≡ false
    summary : String
open SocioeconomicModeratorReceipt public

cpiCreditDistortionReceipt : SocioeconomicModeratorReceipt
cpiCreditDistortionReceipt = socioeconomicModeratorReceipt
  subsidizedRuralCreditExposure
  Authority.cpi2024RuralCreditAuthority
  officialAssociationMapped
  false
  false refl
  "Contemporary policy evidence: 31% of properties with deforestation received subsidized rural credit in 2020-2022 and R$14bn/year of subsidized credit was associated with deforestation; this does not identify the den Braber income coefficient's causal decomposition"

binswangerHistoricalDistortionReceipt : SocioeconomicModeratorReceipt
binswangerHistoricalDistortionReceipt = socioeconomicModeratorReceipt
  historicalTaxCreditDistortion
  Authority.binswanger1991Authority
  historicalMechanismMapped
  false
  false refl
  "Historical peer-reviewed evidence that tax, land-allocation and credit rules encouraged clearing and subsidized inefficient ranching; temporal scope retained"

margulisPrivateProfitReceipt : SocioeconomicModeratorReceipt
margulisPrivateProfitReceipt = socioeconomicModeratorReceipt
  extractiveCommodityProfitability
  Authority.margulis2003Authority
  historicalMechanismMapped
  false
  false refl
  "World Bank analysis emphasizes private viability, liquidity, low-risk and tenure-possession motives for cattle ranching in significant Amazon regions while distinguishing private gains from social/environmental costs"

wriEcosystemExternalityReceipt : SocioeconomicModeratorReceipt
wriEcosystemExternalityReceipt = socioeconomicModeratorReceipt
  ecosystemServiceExternality
  Authority.wriTenureEconomicValuationAuthority
  economicValuationMapped
  false
  false refl
  "WRI valuation estimates 20-year tenure-secure Indigenous-land benefits far exceeding tenure-security costs; this supports an externality/measurement concern but is not a causal decomposition of census household income"

------------------------------------------------------------------------
-- Opportunity-cost asymmetry is represented as valuation context, not a claim
-- that Indigenous territories forego a neutral benchmark of equivalent welfare.
------------------------------------------------------------------------

record OpportunityCostValuationReceipt : Set where
  constructor opportunityCostValuationReceipt
  field
    source : Authority.SourceAuthorityReceipt
    soyAnnualUsdPerHa : Nat
    pastureAnnualUsdPerHa : Nat
    timberAnnualUsdPerHa : Nat
    conversionValueEqualsSocialWelfare : Bool
    conversionValueEqualsSocialWelfareIsFalse : conversionValueEqualsSocialWelfare ≡ false
    indigenousOpportunityCostLogicDirectlyApplicable : Bool
    indigenousOpportunityCostLogicDirectlyApplicableIsFalse : indigenousOpportunityCostLogicDirectlyApplicable ≡ false
    summary : String
open OpportunityCostValuationReceipt public

wriOpportunityCostContext : OpportunityCostValuationReceipt
wriOpportunityCostContext = opportunityCostValuationReceipt
  Authority.wriTenureEconomicValuationAuthority
  450 78 25
  false refl
  false refl
  "WRI report reproduces van Beukering et al. average annual conversion opportunity-cost values of roughly US$450/ha soy, US$78/ha pasture and US$25/ha timber, and explicitly notes this conversion-opportunity-cost logic is not directly applicable to Indigenous land where conversion is not sought/authorized"

------------------------------------------------------------------------
-- LAND BACK component x governance condition -> outcome hyperfabric.
------------------------------------------------------------------------

data GovernanceCondition : Set where
  strongCollectiveTenure : GovernanceCondition
  effectiveIndigenousDecisionAuthority : GovernanceCondition
  externalDispossessionProtection : GovernanceCondition
  stewardshipMaterialCapacity : GovernanceCondition
  transferAndServiceAccess : GovernanceCondition
  extractiveSubsidyPressure : GovernanceCondition
  marketCommodityPressure : GovernanceCondition
  weakCrossOrderEnforcement : GovernanceCondition


data OutcomeKind : Set where
  deforestationOutcome : OutcomeKind
  restorationOutcome : OutcomeKind
  incomeOutcome : OutcomeKind
  inequalityOutcome : OutcomeKind
  employmentOutcome : OutcomeKind
  mentalHealthOutcome : OutcomeKind
  foodSovereigntyOutcome : OutcomeKind
  sovereigntyCapacityOutcome : OutcomeKind


data CausalStatus : Set where
  peerReviewedCausalMapped : CausalStatus
  peerReviewedComparativeMapped : CausalStatus
  systematicReviewMapped : CausalStatus
  workingPaperCausalClaimMapped : CausalStatus
  moderatorHypothesisOpen : CausalStatus


record ComponentModeratorOutcomeEdge : Set where
  constructor componentModeratorOutcomeEdge
  field
    component : Atlas.LandBackComponent
    governanceCondition : GovernanceCondition
    outcome : OutcomeKind
    status : CausalStatus
    sourceReference : String
    exactCrossContextTransportProved : Bool
    exactCrossContextTransportProvedIsFalse : exactCrossContextTransportProved ≡ false
open ComponentModeratorOutcomeEdge public

collectiveTenureDeforestationEdge : ComponentModeratorOutcomeEdge
collectiveTenureDeforestationEdge = componentModeratorOutcomeEdge
  Atlas.collectiveTenureSecurity
  strongCollectiveTenure
  deforestationOutcome
  peerReviewedCausalMapped
  "Baragwanath & Bayi 2020 PNAS collective property-rights causal evidence"
  false refl

collectiveTenureRestorationEdge : ComponentModeratorOutcomeEdge
collectiveTenureRestorationEdge = componentModeratorOutcomeEdge
  Atlas.collectiveTenureSecurity
  strongCollectiveTenure
  restorationOutcome
  peerReviewedCausalMapped
  "Baragwanath, Bayi & Shinde 2023 PNAS secondary-forest causal evidence"
  false refl

landBackUsIncomeEdge : ComponentModeratorOutcomeEdge
landBackUsIncomeEdge = componentModeratorOutcomeEdge
  Atlas.territorialReturnOrRestitution
  effectiveIndigenousDecisionAuthority
  incomeOutcome
  workingPaperCausalClaimMapped
  "Arcoite & Johnson 2025 SSRN working-paper IV/endogenous-treatment result"
  false refl

landBackUsEmploymentEdge : ComponentModeratorOutcomeEdge
landBackUsEmploymentEdge = componentModeratorOutcomeEdge
  Atlas.territorialReturnOrRestitution
  effectiveIndigenousDecisionAuthority
  employmentOutcome
  workingPaperCausalClaimMapped
  "Arcoite & Johnson 2025 SSRN working-paper IV/endogenous-treatment result"
  false refl

extractivePressureIncomeInterpretationEdge : ComponentModeratorOutcomeEdge
extractivePressureIncomeInterpretationEdge = componentModeratorOutcomeEdge
  Atlas.indigenousDecisionAuthority
  extractiveSubsidyPressure
  incomeOutcome
  moderatorHypothesisOpen
  "critical synthesis over den Braber 2024 + CPI 2024 + WRI/World Bank policy evidence; not directly identified by any single study"
  false refl

------------------------------------------------------------------------
-- Refined socioeconomic evidence state.
------------------------------------------------------------------------

data RefinedSocioeconomicState : Set where
  aggregateTradeoffLabelTooCoarse : RefinedSocioeconomicState
  incomePenaltyComparatorSpecific : RefinedSocioeconomicState
  inequalityBenefitComparatorSpecific : RefinedSocioeconomicState
  literacySanitationNoUniformPenalty : RefinedSocioeconomicState
  usWorkingPaperPositiveEconomicSignal : RefinedSocioeconomicState
  governanceModeratorIdentificationOpen : RefinedSocioeconomicState


record RefinedSocioeconomicAtlas : Set where
  constructor refinedSocioeconomicAtlas
  field
    aggregateLabel : RefinedSocioeconomicState
    incomeState : RefinedSocioeconomicState
    inequalityState : RefinedSocioeconomicState
    serviceIndicatorState : RefinedSocioeconomicState
    usEconomicState : RefinedSocioeconomicState
    moderatorState : RefinedSocioeconomicState
    sourceReference : String
open RefinedSocioeconomicAtlas public

currentRefinedSocioeconomicAtlas : RefinedSocioeconomicAtlas
currentRefinedSocioeconomicAtlas = refinedSocioeconomicAtlas
  aggregateTradeoffLabelTooCoarse
  incomePenaltyComparatorSpecific
  inequalityBenefitComparatorSpecific
  literacySanitationNoUniformPenalty
  usWorkingPaperPositiveEconomicSignal
  governanceModeratorIdentificationOpen
  "Socioeconomic outcomes are decomposed by indicator/comparator and source authority; subsidy/externality/governance mechanisms remain separately typed until directly identified"

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data IncomeEqualsWellbeingNeutralMetric : Set where
data IncomePenaltyEqualsIndigenousGovernanceFailure : Set where
data SubsidyExposureExplainsDenBraberIncomeCoefficient : Set where
data WorkingPaperResultEqualsPeerReviewedCausalClosure : Set where
data OpportunityCostEqualsSocialValue : Set where
data LowerMarketIncomeEqualsLowerCommunityWelfare : Set where
data GovernanceModeratorProvedByCrossStudyDifferenceAlone : Set where

incomeIsNotDeclaredWellbeingNeutral : IncomeEqualsWellbeingNeutralMetric → ⊥
incomeIsNotDeclaredWellbeingNeutral ()

incomePenaltyDoesNotProveGovernanceFailure : IncomePenaltyEqualsIndigenousGovernanceFailure → ⊥
incomePenaltyDoesNotProveGovernanceFailure ()

subsidiesDoNotDirectlyExplainCoefficientYet : SubsidyExposureExplainsDenBraberIncomeCoefficient → ⊥
subsidiesDoNotDirectlyExplainCoefficientYet ()

workingPaperDoesNotClosePeerReview : WorkingPaperResultEqualsPeerReviewedCausalClosure → ⊥
workingPaperDoesNotClosePeerReview ()

opportunityCostDoesNotEqualSocialValue : OpportunityCostEqualsSocialValue → ⊥
opportunityCostDoesNotEqualSocialValue ()

lowerMarketIncomeDoesNotAutomaticallyMeanLowerWelfare : LowerMarketIncomeEqualsLowerCommunityWelfare → ⊥
lowerMarketIncomeDoesNotAutomaticallyMeanLowerWelfare ()

crossStudyDifferenceDoesNotProveModerator : GovernanceModeratorProvedByCrossStudyDifferenceAlone → ⊥
crossStudyDifferenceDoesNotProveModerator ()
