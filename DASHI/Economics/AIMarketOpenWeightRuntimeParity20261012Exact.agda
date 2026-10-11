module DASHI.Economics.AIMarketOpenWeightRuntimeParity20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- DASHITRADE RUNTIME-PARITY SNAPSHOTS, 2026-10-12
--
-- These constants mirror source-bounded runtime fixtures from dashiTRADE PR #1.
-- They close only their declared scoped producers. They do not import Python
-- execution authority or promote platform-local/event-level observations into
-- global market claims.
------------------------------------------------------------------------

record OpenWeightPlatformSnapshot : Set where
  constructor openWeightPlatformSnapshot
  field
    observedAt : String
    platform : String
    metric : String
    openWeightShareBp : Nat
    closedWeightShareBp : Nat
    platformLocalPointClosed : Bool
    globalMarketShareClosed : Bool
    sourceURL : String

open OpenWeightPlatformSnapshot public

vercelOpenWeightSnapshot20261010 : OpenWeightPlatformSnapshot
vercelOpenWeightSnapshot20261010 = openWeightPlatformSnapshot
  "2026-10-10"
  "Vercel AI Gateway"
  "token volume share"
  6130
  3870
  true
  false
  "https://vercel.com/api/ai/leaderboard-export?dataset=models"

openWeightPlatformShareBpIs6130 :
  openWeightShareBp vercelOpenWeightSnapshot20261010 ≡ 6130
openWeightPlatformShareBpIs6130 = refl

globalOpenWeightShareStillOpen :
  globalMarketShareClosed vercelOpenWeightSnapshot20261010 ≡ false
globalOpenWeightShareStillOpen = refl

record MarketStressEventSeries : Set where
  constructor marketStressEventSeries
  field
    observedAt : String
    eventCount : Nat
    broadDirectionFlipObserved : Bool
    aiFinancingWindowStressObserved : Bool
    equityMarketCollapseEstablished : Bool
    fixedAIBasketSeriesClosed : Bool
    fixedAIBasketVolatilityClosed : Bool
    fixedAIBasketFlipRateClosed : Bool
    sourceBoundary : String

open MarketStressEventSeries public

marketStressEventSeries20261012 : MarketStressEventSeries
marketStressEventSeries20261012 = marketStressEventSeries
  "2026-10-12"
  4
  true
  true
  false
  false
  false
  false
  "Source-bounded Reuters event series: broad Nasdaq direction reversal plus Firmus AI/data-centre IPO withdrawal; not a fixed-composition AI-equity basket."

broadDirectionFlipObserved :
  MarketStressEventSeries.broadDirectionFlipObserved
    marketStressEventSeries20261012 ≡ true
broadDirectionFlipObserved = refl

aiFinancingWindowStressObserved :
  MarketStressEventSeries.aiFinancingWindowStressObserved
    marketStressEventSeries20261012 ≡ true
aiFinancingWindowStressObserved = refl

fixedAIBasketVolatilityStillOpen :
  fixedAIBasketVolatilityClosed marketStressEventSeries20261012 ≡ false
fixedAIBasketVolatilityStillOpen = refl

fixedAIBasketFlipRateStillOpen :
  fixedAIBasketFlipRateClosed marketStressEventSeries20261012 ≡ false
fixedAIBasketFlipRateStillOpen = refl

------------------------------------------------------------------------
-- Scope firewalls.
------------------------------------------------------------------------

data PlatformShareImpliesGlobalSharePermission : Set where
data BroadIndexFlipImpliesAIBasketFlipPermission : Set where
data IPOWithdrawalImpliesSystemicCollapsePermission : Set where
data RuntimeFixtureImpliesAgdaAuthorityPermission : Set where

platformShareDoesNotAutoPromoteGlobalShare :
  PlatformShareImpliesGlobalSharePermission → ⊥
platformShareDoesNotAutoPromoteGlobalShare ()

broadIndexFlipDoesNotAutoPromoteAIBasketFlip :
  BroadIndexFlipImpliesAIBasketFlipPermission → ⊥
broadIndexFlipDoesNotAutoPromoteAIBasketFlip ()

ipoWithdrawalDoesNotAutoProveSystemicCollapse :
  IPOWithdrawalImpliesSystemicCollapsePermission → ⊥
ipoWithdrawalDoesNotAutoProveSystemicCollapse ()

runtimeFixtureDoesNotAutoCreateAgdaAuthority :
  RuntimeFixtureImpliesAgdaAuthorityPermission → ⊥
runtimeFixtureDoesNotAutoCreateAgdaAuthority ()

runtimeParityBoundary : String
runtimeParityBoundary =
  "The Vercel 2026-10-10 point closes a platform-local token-share producer at 61.3 percent open-weight / 38.7 percent closed-weight. The 2026-10-12 event series closes event-level evidence for a broad-index direction flip and AI financing-window stress. Global open-weight share, capability equivalence, fixed AI-basket series, volatility and flip-rate remain separate unpaid producers."
