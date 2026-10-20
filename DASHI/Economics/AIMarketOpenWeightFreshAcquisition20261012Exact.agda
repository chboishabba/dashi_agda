module DASHI.Economics.AIMarketOpenWeightFreshAcquisition20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- FRESH OCTOBER-12 MARKET / OPEN-WEIGHT ACQUISITION
--
-- This owner upgrades two previously stale/no-evidence surfaces without
-- laundering a broad-index event series into the still-missing fixed AI basket.
------------------------------------------------------------------------

primaryPlatformTelemetryKind : Source.SourceKind
primaryPlatformTelemetryKind = Source.namedSourceKind "primary platform telemetry"

vercelLeaderboard20261010 : Source.AttributedSource
vercelLeaderboard20261010 = Source.mkNoDOISource
  "Vercel"
  "AI model leaderboards"
  "Vercel AI Gateway"
  "2026-10-10"
  "https://vercel.com/ai-gateway/leaderboards/models"
  primaryPlatformTelemetryKind
  "primary platform-local carrier for 61.3 percent open-weight versus 38.7 percent closed-weight token volume on the latest chart date; data are CC BY 4.0 and do not represent the entire AI market"
  Source.publicAttribution

vercelLeaderboardExportDocs2026 : Source.AttributedSource
vercelLeaderboardExportDocs2026 = Source.mkNoDOISource
  "Vercel"
  "Access and share AI Gateway leaderboard data"
  "Vercel changelog"
  "2026-07-14"
  "https://vercel.com/changelog/open-data-and-shareable-charts-for-ai-gateway-leaderboards"
  primaryPlatformTelemetryKind
  "primary documentation for the daily leaderboard-export API and CC BY 4.0 time-series access"
  Source.publicAttribution

reutersMarketDown20261008 : Source.AttributedSource
reutersMarketDown20261008 = Source.mkNoDOISource
  "Reuters"
  "S&P 500, Nasdaq end lower as crude prices jump, chip stocks weigh"
  "Reuters"
  "2026-10-08"
  "https://www.reuters.com/business/wall-st-futures-slide-rising-oil-yields-dampen-mood-2026-10-08/"
  Source.newsSource
  "secondary carrier for Nasdaq -1.25 percent and S&P 500 -0.47 percent on a day where chip stocks and AI-financing concerns weighed"
  Source.publicAttribution

reutersMarketRebound20261009 : Source.AttributedSource
reutersMarketRebound20261009 = Source.mkNoDOISource
  "Reuters"
  "Stocks advance ahead of earnings, navigating still-high Treasury yields and oil prices"
  "Reuters"
  "2026-10-09"
  "https://www.reuters.com/world/china/global-markets-wrapup-1-2026-10-09/"
  Source.newsSource
  "secondary carrier for roughly +0.6 percent S&P 500 and Nasdaq rebound while financing conditions remained tight"
  Source.publicAttribution

reutersFirmusIPO20261009 : Source.AttributedSource
reutersFirmusIPO20261009 = Source.mkNoDOISource
  "Reuters"
  "Firmus $5 bln float failure deals blow to Australia's shrinking share market"
  "Reuters"
  "2026-10-09"
  "https://www.reuters.com/legal/transactional/firmus-5-bln-float-failure-deals-blow-australias-shrinking-share-market-2026-10-09/"
  Source.newsSource
  "secondary carrier for withdrawal of the planned A$5B Firmus AI/data-centre IPO amid market volatility and a shift toward private funding"
  Source.publicAttribution

record OpenWeightPlatformSnapshot : Set where
  constructor openWeightPlatformSnapshot
  field
    observationDate : String
    openWeightTokenShareBp : Nat
    closedWeightTokenShareBp : Nat
    platformLocalPointClosed : Bool
    globalMarketShareClosed : Bool
    source : Source.AttributedSource

open OpenWeightPlatformSnapshot public

vercelOpenWeightSnapshot20261010 : OpenWeightPlatformSnapshot
vercelOpenWeightSnapshot20261010 = openWeightPlatformSnapshot
  "2026-10-10" 6130 3870 true false vercelLeaderboard20261010

record MarketEventEvidence : Set where
  constructor marketEventEvidence
  field
    broadDirectionFlipObserved : Bool
    aiFinancingWindowStressObserved : Bool
    fixedAIBasketSeriesClosed : Bool
    fixedAIBasketVolatilityClosed : Bool
    fixedAIBasketFlipRateClosed : Bool
    equityMarketCollapseEstablished : Bool

open MarketEventEvidence public

currentMarketEventEvidence20261012 : MarketEventEvidence
currentMarketEventEvidence20261012 = marketEventEvidence
  true true false false false false

record FreshAcquisitionBoundary : Set where
  constructor freshAcquisitionBoundary
  field
    openWeightPointImproved : Bool
    broadMarketEventEvidenceImproved : Bool
    fixedBasketResidualStillOpen : Bool
    globalOpenWeightShareStillOpen : Bool

open FreshAcquisitionBoundary public

currentFreshAcquisitionBoundary : FreshAcquisitionBoundary
currentFreshAcquisitionBoundary = freshAcquisitionBoundary true true true true

------------------------------------------------------------------------
-- Non-promotion firewalls.
------------------------------------------------------------------------

data GatewayShareImpliesGlobalSharePermission : Set where
data BroadFlipImpliesFixedBasketFlipPermission : Set where
data IPOWithdrawalImpliesSystemicCrisisPermission : Set where

gatewayShareDoesNotAutoBecomeGlobalShare : GatewayShareImpliesGlobalSharePermission → ⊥
gatewayShareDoesNotAutoBecomeGlobalShare ()

broadIndexFlipDoesNotAutoCloseFixedAIBasket : BroadFlipImpliesFixedBasketFlipPermission → ⊥
broadIndexFlipDoesNotAutoCloseFixedAIBasket ()

ipoWithdrawalDoesNotAutoProveSystemicCrisis : IPOWithdrawalImpliesSystemicCrisisPermission → ⊥
ipoWithdrawalDoesNotAutoProveSystemicCrisis ()

openWeightPointIs6130bp : openWeightTokenShareBp vercelOpenWeightSnapshot20261010 ≡ 6130
openWeightPointIs6130bp = refl

globalOpenWeightShareStillUnclosed : globalMarketShareClosed vercelOpenWeightSnapshot20261010 ≡ false
globalOpenWeightShareStillUnclosed = refl

fixedBasketStillUnclosed : fixedAIBasketSeriesClosed currentMarketEventEvidence20261012 ≡ false
fixedBasketStillUnclosed = refl
