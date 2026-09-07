module DASHI.Cognition.PNF.SensibLawIndigenousCarbonValueComparabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawIndigenousLandBackSourceAuthorityExact as Source

------------------------------------------------------------------------
-- Carbon-value comparability boundary.
--
-- WRI social/economic valuation, commercial REDD+ market prices, government
-- research case estimates and BIA legal/administrative classification are four
-- different proposition types.  Matching the word "carbon" does not make the
-- values numerically or semantically commensurable.
------------------------------------------------------------------------

data CarbonQuantityUnit : Set where
  usdPerHectarePerYear : CarbonQuantityUnit
  usdPerTonneCO2e : CarbonQuantityUnit
  usdPerProjectPerYear : CarbonQuantityUnit
  legalCategoryNoNumericUnit : CarbonQuantityUnit


data CarbonValueRole : Set where
  tenureSecurityCost : CarbonValueRole
  socialCarbonMitigationValue : CarbonValueRole
  voluntaryMarketCreditPrice : CarbonValueRole
  illustrativeProjectRevenue : CarbonValueRole
  agencyTrustAssetClassification : CarbonValueRole


record CarbonValueObservation : Set where
  constructor carbonValueObservation
  field
    source : Source.SourceAuthorityReceipt
    role : CarbonValueRole
    unit : CarbonQuantityUnit
    lowerWholeUsd : Nat
    upperWholeUsd : Nat
    exactWholeDollarEncoding : Bool
    sourceClaimReference : String
    causalEffectClaimed : Bool
    causalEffectClaimedIsFalse : causalEffectClaimed ≡ false
open CarbonValueObservation public

wriBrazilTenureCost : CarbonValueObservation
wriBrazilTenureCost = carbonValueObservation
  Source.wriTenureEconomicValuationAuthority
  tenureSecurityCost
  usdPerHectarePerYear
  1 2
  false
  "WRI reports average annual Brazil tenure-security cost of USD 1.57/ha; whole-dollar interval [1,2] is stored here only as a bounded carrier, not as replacement for the decimal source value"
  false refl

wriBrazilCarbonMitigationValue : CarbonValueObservation
wriBrazilCarbonMitigationValue = carbonValueObservation
  Source.wriTenureEconomicValuationAuthority
  socialCarbonMitigationValue
  usdPerHectarePerYear
  38 230
  true
  "WRI reports estimated carbon-mitigation benefits of USD 38-230/ha/year for the Brazil analysis"
  false refl

abatableBrazilReddMedianQ1_2025 : CarbonValueObservation
abatableBrazilReddMedianQ1_2025 = carbonValueObservation
  Source.abatable2025ReddPriceAuthority
  voluntaryMarketCreditPrice
  usdPerTonneCO2e
  2 3
  false
  "Abatable reports median Brazil REDD+ carbon-credit spot price USD 2.50/unit at end-Q1 2025; whole-dollar interval [2,3] preserves unit class without replacing the source decimal"
  false refl

embrapaPoyanawaIllustrativeAnnualRevenue : CarbonValueObservation
embrapaPoyanawaIllustrativeAnnualRevenue = carbonValueObservation
  Source.embrapaPoyanawa2021Authority
  illustrativeProjectRevenue
  usdPerProjectPerYear
  38286 38286
  true
  "Embrapa communication reports illustrative annual revenue USD 38,286 from 6,381 tCO2/year at an assumed USD 6/tCO2 in the Poyanawa case"
  false refl

------------------------------------------------------------------------
-- Same-unit comparison is a precondition for direct numeric gap claims.
------------------------------------------------------------------------

data UnitComparability : Set where
  sameFunctionalUnit : UnitComparability
  conversionReceiptRequired : UnitComparability
  incomparableWithoutAdditionalMapping : UnitComparability


unitComparability : CarbonQuantityUnit → CarbonQuantityUnit → UnitComparability
unitComparability usdPerHectarePerYear usdPerHectarePerYear = sameFunctionalUnit
unitComparability usdPerTonneCO2e usdPerTonneCO2e = sameFunctionalUnit
unitComparability usdPerProjectPerYear usdPerProjectPerYear = sameFunctionalUnit
unitComparability legalCategoryNoNumericUnit legalCategoryNoNumericUnit = sameFunctionalUnit
unitComparability usdPerHectarePerYear usdPerTonneCO2e = conversionReceiptRequired
unitComparability usdPerTonneCO2e usdPerHectarePerYear = conversionReceiptRequired
unitComparability _ _ = incomparableWithoutAdditionalMapping

wriVsAbatableNeedsConversion :
  unitComparability
    (unit wriBrazilCarbonMitigationValue)
    (unit abatableBrazilReddMedianQ1_2025)
  ≡ conversionReceiptRequired
wriVsAbatableNeedsConversion = refl

record DirectGapClaimBoundary : Set where
  constructor directGapClaimBoundary
  field
    left right : CarbonValueObservation
    comparability : UnitComparability
    exactDirectUndercompensationRatioClaimed : Bool
    exactDirectUndercompensationRatioClaimedIsFalse : exactDirectUndercompensationRatioClaimed ≡ false
    missingMapping : String
open DirectGapClaimBoundary public

wriMarketGapBoundary : DirectGapClaimBoundary
wriMarketGapBoundary = directGapClaimBoundary
  wriBrazilCarbonMitigationValue
  abatableBrazilReddMedianQ1_2025
  conversionReceiptRequired
  false refl
  "Need a source-backed common functional unit (e.g. tCO2e/ha/year for the same intervention/context) before calculating a direct valuation-to-market compensation ratio"

------------------------------------------------------------------------
-- Source roles remain distinct.
------------------------------------------------------------------------

wriIsValuationReport :
  Source.authorityKind Source.wriTenureEconomicValuationAuthority ≡ Source.economicValuationReport
wriIsValuationReport = refl

abatableIsCommercialMarketObservation :
  Source.authorityKind Source.abatable2025ReddPriceAuthority ≡ Source.commercialMarketObservation
abatableIsCommercialMarketObservation = refl

embrapaIsGovernmentResearchCommunication :
  Source.authorityKind Source.embrapaPoyanawa2021Authority ≡ Source.governmentResearchCommunication
embrapaIsGovernmentResearchCommunication = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data SameWordCarbonMakesValuesCommensurable : Set where
data PerTonnePriceEqualsPerHectareSocialValue : Set where
data MarketPriceProvesFairCompensation : Set where
data SocialValuationProvesRealisedCommunityRevenue : Set where

carbonLabelDoesNotMakeCommensurable : SameWordCarbonMakesValuesCommensurable → ⊥
carbonLabelDoesNotMakeCommensurable ()
perTonnePriceDoesNotEqualPerHectareValue : PerTonnePriceEqualsPerHectareSocialValue → ⊥
perTonnePriceDoesNotEqualPerHectareValue ()
marketPriceDoesNotProveFairCompensation : MarketPriceProvesFairCompensation → ⊥
marketPriceDoesNotProveFairCompensation ()
valuationDoesNotProveRealisedRevenue : SocialValuationProvesRealisedCommunityRevenue → ⊥
valuationDoesNotProveRealisedCommunityRevenue ()
