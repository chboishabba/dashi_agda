module DASHI.Economics.AICoreWeave2032BondRepricing20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

secKind : Source.SourceKind
secKind = Source.namedSourceKind "SEC-filed bond issuance"

marketKind : Source.SourceKind
marketKind = Source.namedSourceKind "secondary financial-market reporting"

coreWeave2032IssuanceSource : Source.AttributedSource
coreWeave2032IssuanceSource = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Current Report: 9.625% Senior Notes due 2032"
  "SEC filing"
  "2026-06-18"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000291/crwv-20260618.htm"
  secKind
  "USD1.25B aggregate principal amount of 9.625 percent senior notes due July 15 2032"
  Source.publicAttribution

coreWeave2032MarketSource : Source.AttributedSource
coreWeave2032MarketSource = Source.mkNoDOISource
  "Reuters"
  "Morning Bid: Market picks CoreWeave as AI rout deepens"
  "secondary financial-market report"
  "2026-10-15"
  "https://www.reuters.com/world/china/global-markets-view-europe-2026-10-15/"
  marketKind
  "reports yields on CoreWeave 2032 bonds above 15 percent during the October credit selloff"
  Source.publicAttribution

record BondRepricing : Set where
  constructor bond-repricing
  field
    issueCouponTenThousandthsPercent : Nat
    octoberYieldLowerBoundTenThousandthsPercent : Nat
    yieldIncreaseLowerBoundTenThousandthsPercent : Nat
    sameInstrumentLongitudinalRepricing : Bool
    defaultOccurred : Bool
    realisedRefinancingCostPaid : Bool
    companyWideDebtCostIdentified : Bool

open BondRepricing public

coreWeave2032BondRepricing : BondRepricing
coreWeave2032BondRepricing = bond-repricing
  9625 15000 5375 true false false false

issueCouponTenThousandthsPercentIs9625 :
  issueCouponTenThousandthsPercent coreWeave2032BondRepricing ≡ 9625
issueCouponTenThousandthsPercentIs9625 = refl

octoberYieldLowerBoundTenThousandthsPercentIs15000 :
  octoberYieldLowerBoundTenThousandthsPercent coreWeave2032BondRepricing ≡ 15000
octoberYieldLowerBoundTenThousandthsPercentIs15000 = refl

yieldIncreaseLowerBoundTenThousandthsPercentIs5375 :
  yieldIncreaseLowerBoundTenThousandthsPercent coreWeave2032BondRepricing ≡ 5375
yieldIncreaseLowerBoundTenThousandthsPercentIs5375 = refl

sameInstrumentLongitudinalRepricingPaid :
  sameInstrumentLongitudinalRepricing coreWeave2032BondRepricing ≡ true
sameInstrumentLongitudinalRepricingPaid = refl

data SecondaryYieldCreatesOccurredDefaultPermission : Set where
data SecondaryYieldCreatesRefinancingCostPermission : Set where

secondaryYieldDoesNotCreateOccurredDefault : SecondaryYieldCreatesOccurredDefaultPermission → ⊥
secondaryYieldDoesNotCreateOccurredDefault ()

secondaryYieldDoesNotCreateRealisedRefinancingCost : SecondaryYieldCreatesRefinancingCostPermission → ⊥
secondaryYieldDoesNotCreateRealisedRefinancingCost ()

boundary : String
boundary =
  "CoreWeave's June-18 primary filing identifies the USD 9.625 percent senior notes due 2032; Reuters on October 15 reports yields on CoreWeave 2032 bonds above 15 percent. The selected same-maturity/coupon instrument therefore pays a longitudinal secondary-market repricing of at least 5.375 percentage points relative to its issue coupon. This is a market-required-yield observation, not an occurred default, realised refinancing transaction, company-wide debt cost, or proof that the notes will ultimately incur loss."
