module DASHI.Economics.AIFrontierAdjustedProfitabilityCounterweight20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

secondaryInvestorReportingKind : Source.SourceKind
secondaryInvestorReportingKind = Source.namedSourceKind "secondary reporting of private-company investor disclosure"

reutersAnthropicInvestorDay : Source.AttributedSource
reutersAnthropicInvestorDay = Source.mkNoDOISource
  "Reuters"
  "Anthropic's Q3 revenue surges 45% to nearly $17 billion"
  "secondary report of investor-day statements"
  "2026-10-14"
  "https://www.reuters.com/business/finance/anthropics-q3-revenue-surges-45-nearly-17-billion-2026-10-14/"
  secondaryInvestorReportingKind
  "Reuters reports attendees saying Anthropic disclosed Q3 revenue of 16.8 billion dollars, up 45 percent quarter over quarter, and said it was profitable on an adjusted basis. Reuters also notes very large future cloud/infrastructure commitments and prior operating losses."
  Source.publicAttribution

record FrontierProfitabilityCounterweight : Set where
  constructor frontier-profitability-counterweight
  field
    q3RevenueTenthsBillionsUSD : Nat
    qoqRevenueGrowthPercent : Nat
    adjustedProfitabilityReported : Bool
    auditedGAAPProfitabilityPaid : Bool
    freeCashFlowPositivePaid : Bool
    roicAboveWaccPaid : Bool
    durableFrontierRentEstablished : Bool
    allFrontierLabsUnprofitableEstablished : Bool

open FrontierProfitabilityCounterweight public

anthropicQ3Counterweight : FrontierProfitabilityCounterweight
anthropicQ3Counterweight = frontier-profitability-counterweight
  168 45 true false false false false false

adjustedProfitabilityReportedPaid : adjustedProfitabilityReported anthropicQ3Counterweight ≡ true
adjustedProfitabilityReportedPaid = refl

data AdjustedProfitImpliesGAAPPermission : Set where
data OneFrontierFirmImpliesDurableRentRegimePermission : Set where
data LargeInfrastructureCommitmentNegatesCurrentAdjustedProfitPermission : Set where

adjustedProfitDoesNotCreateGAAPProfit : AdjustedProfitImpliesGAAPPermission → ⊥
adjustedProfitDoesNotCreateGAAPProfit ()

oneFirmDoesNotSelectDurableRentRegime : OneFrontierFirmImpliesDurableRentRegimePermission → ⊥
oneFirmDoesNotSelectDurableRentRegime ()

futureCommitmentDoesNotEraseReportedCurrentAdjustment : LargeInfrastructureCommitmentNegatesCurrentAdjustedProfitPermission → ⊥
futureCommitmentDoesNotEraseReportedCurrentAdjustment ()

boundary : String
boundary =
  "Reuters reports that Anthropic told prospective investors Q3 2026 revenue was 16.8 billion dollars, up 45 percent quarter over quarter, and that the company was profitable on an adjusted basis. This is a material counterweight to the claim that frontier labs cannot reach any profitability measure. The report is secondary evidence about a private-company investor disclosure, not audited GAAP accounts, free cash flow, ROIC-WACC or a durable-rent theorem; the same reporting context also contains very large future infrastructure commitments and historical losses. Neither the bullish nor bearish promotion is manufactured."
