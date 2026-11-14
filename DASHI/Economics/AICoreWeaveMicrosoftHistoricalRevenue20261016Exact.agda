module DASHI.Economics.AICoreWeaveMicrosoftHistoricalRevenue20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

secFilingKind : Source.SourceKind
secFilingKind = Source.namedSourceKind "primary SEC annual/quarterly filing"

coreWeave2025AnnualSource : Source.AttributedSource
coreWeave2025AnnualSource = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Annual report for year ended December 31 2025"
  "SEC Form 10-K"
  "2026"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000104/crwv-20251231.htm"
  secFilingKind
  "reports 2025 revenue of approximately USD5.131B and identifies Microsoft as approximately 67 percent of annual revenue"
  Source.publicAttribution

coreWeaveQ22026Source : Source.AttributedSource
coreWeaveQ22026Source = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Quarterly report for period ended June 30 2026"
  "SEC Form 10-Q"
  "2026-08-12"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000366/crwv-20260630.htm"
  secFilingKind
  "reports significant customers using anonymised letter labels and states that a letter may represent different customers across periods; therefore historical Microsoft identity does not de-anonymise 2026 Customer A/B/C"
  Source.publicAttribution

record HistoricalNamedRevenue : Set where
  constructor historical-named-revenue
  field
    annualRevenueMillionUSD : Nat
    microsoftRevenueSharePercent : Nat
    microsoftRecognisedRevenueMillionUSDApprox : Nat
    historicalNamedRevenue : Bool
    namedCashCollection : Bool
    identifies2026CustomerA : Bool
    exhaustiveTerminalPayerGraph : Bool

open HistoricalNamedRevenue public

coreWeaveMicrosoft2025Revenue : HistoricalNamedRevenue
coreWeaveMicrosoft2025Revenue = historical-named-revenue
  5131 67 3438 true false false false

annualRevenueMillionUSDIs5131 : annualRevenueMillionUSD coreWeaveMicrosoft2025Revenue ≡ 5131
annualRevenueMillionUSDIs5131 = refl

microsoftRevenueSharePercentIs67 : microsoftRevenueSharePercent coreWeaveMicrosoft2025Revenue ≡ 67
microsoftRevenueSharePercentIs67 = refl

microsoftRecognisedRevenueMillionUSDApproxIs3438 :
  microsoftRecognisedRevenueMillionUSDApprox coreWeaveMicrosoft2025Revenue ≡ 3438
microsoftRecognisedRevenueMillionUSDApproxIs3438 = refl

historicalNamedRevenuePaid : historicalNamedRevenue coreWeaveMicrosoft2025Revenue ≡ true
historicalNamedRevenuePaid = refl

data NamedRevenueCreatesNamedCashPermission : Set where
data HistoricalMicrosoftIdentifies2026CustomerAPermission : Set where

namedRevenueDoesNotCreateNamedCash : NamedRevenueCreatesNamedCashPermission → ⊥
namedRevenueDoesNotCreateNamedCash ()

historicalMicrosoftDoesNotIdentify2026CustomerA : HistoricalMicrosoftIdentifies2026CustomerAPermission → ⊥
historicalMicrosoftDoesNotIdentify2026CustomerA ()

boundary : String
boundary =
  "CoreWeave's 2025 annual filing pays a historical named realised-revenue edge: Microsoft represented approximately 67 percent of approximately USD5.131B annual revenue, implying about USD3.438B of recognised revenue under the rounded filing figures. Recognised revenue is not payer-specific cash collection. The 2026 quarterly filing deliberately uses anonymised customer letters and warns that letter identities can differ between periods, so the historical Microsoft edge cannot de-anonymise 2026 Customer A/B/C or close the current terminal-payer graph."
