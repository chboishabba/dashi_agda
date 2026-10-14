module DASHI.Economics.AICerebrasProviderCostComposition20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

primarySECFiling : Source.SourceKind
primarySECFiling = Source.namedSourceKind "primary SEC filing"

cerebrasQ12026Source : Source.AttributedSource
cerebrasQ12026Source = Source.mkNoDOISource
  "Cerebras Systems Inc."
  "Form 10-Q for quarter ended March 31 2026"
  "SEC quarterly filing"
  "2026-05"
  "https://www.sec.gov/Archives/edgar/data/2021728/000162828026044981/cbrs-20260331.htm"
  primarySECFiling
  "reports Q1-2026 cloud-and-other-services cost of revenue USD 42.299M, up USD 32.801M year over year; the increase was primarily due to USD 28.8M more data-center costs including depreciation and USD 4.0M more pass-through data-center costs; cloud gross margin improved due to higher pricing and improved capacity utilisation"
  Source.publicAttribution

cerebrasQ22026Source : Source.AttributedSource
cerebrasQ22026Source = Source.mkNoDOISource
  "Cerebras Systems Inc."
  "Form 10-Q for quarter ended June 30 2026"
  "SEC quarterly filing"
  "2026-08-12"
  "https://www.sec.gov/Archives/edgar/data/2021728/000162828026056357/cbrs-20260630.htm"
  primarySECFiling
  "reports Q2-2026 cloud-and-other-services revenue USD 125.991M and cost of revenue USD 101.410M; the segment cost definition includes data-center costs, depreciation or equipment rental, personnel and facilities"
  Source.publicAttribution

record ProviderSegmentCostComposition : Set where
  constructor provider-segment-cost-composition
  field
    q1CloudCostThousandUSD : Nat
    q1CloudCostIncreaseThousandUSD : Nat
    q1DataCenterIncreaseInclDepreciationThousandUSD : Nat
    q1PassThroughIncreaseThousandUSD : Nat
    q1NarrativeRoundedResidualThousandUSD : Nat
    q2CloudRevenueThousandUSD : Nat
    q2CloudCostThousandUSD : Nat
    providerSegmentCostCompositionObserved : Bool
    utilizationSensitivityObserved : Bool
    pureInferenceCostIsolated : Bool
    tokenDenominatorPaid : Bool
    marginalTokenCostPaid : Bool

open ProviderSegmentCostComposition public

cerebrasProviderCostComposition : ProviderSegmentCostComposition
cerebrasProviderCostComposition = provider-segment-cost-composition
  42299 32801 28800 4000 1 125991 101410 true true false false false

q1CloudCostMillionThousandUSDIs42299 :
  q1CloudCostThousandUSD cerebrasProviderCostComposition ≡ 42299
q1CloudCostMillionThousandUSDIs42299 = refl

q1CloudCostIncreaseThousandUSDIs32801 :
  q1CloudCostIncreaseThousandUSD cerebrasProviderCostComposition ≡ 32801
q1CloudCostIncreaseThousandUSDIs32801 = refl

q1DataCenterIncreaseInclDepreciationThousandUSDIs28800 :
  q1DataCenterIncreaseInclDepreciationThousandUSD cerebrasProviderCostComposition ≡ 28800
q1DataCenterIncreaseInclDepreciationThousandUSDIs28800 = refl

q1PassThroughIncreaseThousandUSDIs4000 :
  q1PassThroughIncreaseThousandUSD cerebrasProviderCostComposition ≡ 4000
q1PassThroughIncreaseThousandUSDIs4000 = refl

-- The narrative drivers are rounded to one decimal million; retain the 1k
-- residual rather than pretending the prose decomposition is exact accounting.
q1RoundedNarrativeReconciliation : 28800 + 4000 + 1 ≡ 32801
q1RoundedNarrativeReconciliation = refl

q2CloudCostThousandUSDIs101410 :
  q2CloudCostThousandUSD cerebrasProviderCostComposition ≡ 101410
q2CloudCostThousandUSDIs101410 = refl

providerSegmentCostCompositionPaid :
  providerSegmentCostCompositionObserved cerebrasProviderCostComposition ≡ true
providerSegmentCostCompositionPaid = refl

data SegmentCostCreatesMarginalTokenCostPermission : Set where
data UtilizationStatementCreatesTokenDenominatorPermission : Set where
data SegmentCostEqualsPureInferenceCostPermission : Set where

segmentCostDoesNotCreateMarginalTokenCost : SegmentCostCreatesMarginalTokenCostPermission → ⊥
segmentCostDoesNotCreateMarginalTokenCost ()

utilizationStatementDoesNotCreateTokenDenominator : UtilizationStatementCreatesTokenDenominatorPermission → ⊥
utilizationStatementDoesNotCreateTokenDenominator ()

segmentCostDoesNotEqualPureInferenceCost : SegmentCostEqualsPureInferenceCostPermission → ⊥
segmentCostDoesNotEqualPureInferenceCost ()

boundary : String
boundary =
  "Cerebras primary filings now pay a provider-side segment cost-composition surface, not merely gross margin. Q1-2026 cloud-and-other-services cost of revenue was USD 42.299M, up USD 32.801M year over year; management attributes the increase primarily to about USD 28.8M of additional data-center costs including depreciation and USD 4.0M of pass-through data-center costs, and says higher pricing plus improved capacity utilisation improved cloud margin. Q2 cloud-and-other-services cost of revenue was USD 101.410M on USD 125.991M revenue. The segment also includes support/other services, personnel, facilities, depreciation/rental and pass-through costs; no matched token/workload denominator is disclosed. Therefore segment cost composition and utilisation sensitivity are paid, while pure-inference marginal cost per token remains open."
