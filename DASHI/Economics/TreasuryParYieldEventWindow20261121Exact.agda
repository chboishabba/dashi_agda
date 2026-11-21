module DASHI.Economics.TreasuryParYieldEventWindow20261121Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

-- Official US Treasury 2026 daily par CMT, fixed tenor, indicative OTC bid
-- quotes near 15:30 ET. Hundreds of percent: 467 = 4.67% = 467 bp.
-- NOT actual auction stop-out yields or observed trade executions.
-- Source https://home.treasury.gov/resource-center/data-chart-center/interest-rates/TextView?field_tdr_date_value=2026&type=daily_treasury_yield_curve
-- Published/acquired historical dataset used for retrospective reasoning;
-- exact contemporaneous publication timestamps not acquired here.
record TreasuryDailyClose : Set where
  constructor treasuryDailyClose
  field
    day : String
    tenYearBasisPoints : Nat
    thirtyYearBasisPoints : Nat
    source : String
open TreasuryDailyClose public

sourceURL : String
sourceURL =
  "https://home.treasury.gov/resource-center/data-chart-center/interest-rates/TextView?field_tdr_date_value=2026&type=daily_treasury_yield_curve"

july29 : TreasuryDailyClose
july29 = treasuryDailyClose "2026-07-29" 467 520 sourceURL

july30 : TreasuryDailyClose
july30 = treasuryDailyClose "2026-07-30" 468 521 sourceURL

july31 : TreasuryDailyClose
july31 = treasuryDailyClose "2026-07-31" 475 527 sourceURL

august03 : TreasuryDailyClose
august03 = treasuryDailyClose "2026-08-03" 470 523 sourceURL

july31TenYearUpSeven : tenYearBasisPoints july30 + 7 ≡ tenYearBasisPoints july31
july31TenYearUpSeven = refl

july31ThirtyYearUpSix : thirtyYearBasisPoints july30 + 6 ≡ thirtyYearBasisPoints july31
july31ThirtyYearUpSix = refl

august03TenYearBelowJuly31 : tenYearBasisPoints august03 + 5 ≡ tenYearBasisPoints july31
august03TenYearBelowJuly31 = refl

august03ThirtyYearBelowJuly31 : thirtyYearBasisPoints august03 + 4 ≡ thirtyYearBasisPoints july31
august03ThirtyYearBelowJuly31 = refl

windowTenYearThreeBpHigher : tenYearBasisPoints july29 + 3 ≡ tenYearBasisPoints august03
windowTenYearThreeBpHigher = refl

windowThirtyYearThreeBpHigher : thirtyYearBasisPoints july29 + 3 ≡ thirtyYearBasisPoints august03
windowThirtyYearThreeBpHigher = refl

data CMTObservationImpliesYieldCausation : Set where
data YieldChangeProvesCheaperRefunding : Set where
data YieldChangeProvesPolicyIntent : Set where

dailyParYieldDoesNotIsolateInterventionEffect :
  CMTObservationImpliesYieldCausation → ⊥
dailyParYieldDoesNotIsolateInterventionEffect ()

secondaryQuoteDoesNotProveFundingBenefit :
  YieldChangeProvesCheaperRefunding → ⊥
secondaryQuoteDoesNotProveFundingBenefit ()

secondaryQuoteDoesNotProvePolicyIntent :
  YieldChangeProvesPolicyIntent → ⊥
secondaryQuoteDoesNotProvePolicyIntent ()
