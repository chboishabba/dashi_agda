module DASHI.Economics.AIFixedBasketMarketSeries20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- FIXED-COMPOSITION PUBLIC-EQUITY BASKET, OCTOBER 1-9 2026
--
-- Equal-weight CRWV / ORCL / AVGO daily simple returns over seven sessions.
-- This pays a selected-basket market-series producer. It does not represent
-- private labs, credit, SPVs, all AI equities or a universal market state.
------------------------------------------------------------------------

secondaryMarketHistoryKind : Source.SourceKind
secondaryMarketHistoryKind = Source.namedSourceKind "secondary public market-price history"

coreWeaveHistorySource : Source.AttributedSource
coreWeaveHistorySource = Source.mkNoDOISource
  "ChartExchange"
  "CRWV Historical Prices"
  "ChartExchange"
  "2026-10-09"
  "https://chartexchange.com/symbol/nasdaq-crwv/historical/"
  secondaryMarketHistoryKind
  "secondary market-data carrier for CoreWeave daily closes/returns over the declared October 1-9 window"
  Source.publicAttribution

oracleHistorySource : Source.AttributedSource
oracleHistorySource = Source.mkNoDOISource
  "ChartExchange"
  "ORCL Historical Prices"
  "ChartExchange"
  "2026-10-09"
  "https://chartexchange.com/symbol/nyse-orcl/historical/"
  secondaryMarketHistoryKind
  "secondary market-data carrier for Oracle daily closes/returns over the declared October 1-9 window"
  Source.publicAttribution

broadcomHistorySource : Source.AttributedSource
broadcomHistorySource = Source.mkNoDOISource
  "ChartExchange"
  "AVGO Historical Prices"
  "ChartExchange"
  "2026-10-09"
  "https://chartexchange.com/symbol/nasdaq-avgo/historical/"
  secondaryMarketHistoryKind
  "secondary market-data carrier for Broadcom daily closes/returns over the declared October 1-9 window"
  Source.publicAttribution

record FixedBasketDefinition : Set where
  constructor fixedBasketDefinition
  field
    basketId : String
    memberCount : Nat
    sessionCount : Nat
    weighting : String
    horizonStart : String
    horizonEnd : String

open FixedBasketDefinition public

selectedAICapitalBasket : FixedBasketDefinition
selectedAICapitalBasket = fixedBasketDefinition
  "ai-capital-equalweight-crwv-orcl-avgo-v1"
  3 7 "equal-weight daily simple returns" "2026-10-01" "2026-10-09"

record FixedBasketResult : Set where
  constructor fixedBasketResult
  field
    flipCount : Nat
    transitionCount : Nat
    flipRateBp : Nat
    populationDailyVolatilityPpm : Nat
    meanDailyReturnPpm : Nat
    selectedBasketFlipRateClosed : Bool
    selectedBasketVolatilityClosed : Bool
    globalAIMarketFlipRateClosed : Bool
    globalAIMarketVolatilityClosed : Bool

open FixedBasketResult public

selectedAICapitalBasketResult : FixedBasketResult
selectedAICapitalBasketResult = fixedBasketResult
  4 6 6667 28644 483 true true false false

------------------------------------------------------------------------
-- Scope firewalls.
------------------------------------------------------------------------

data SelectedBasketImpliesGlobalMarketPermission : Set where
data EquityBasketImpliesCreditStressPermission : Set where
data SevenSessionVolImpliesStructuralRegimePermission : Set where

selectedBasketDoesNotAutoBecomeGlobalMarket : SelectedBasketImpliesGlobalMarketPermission → ⊥
selectedBasketDoesNotAutoBecomeGlobalMarket ()

equityBasketDoesNotAutoBecomeCreditStress : EquityBasketImpliesCreditStressPermission → ⊥
equityBasketDoesNotAutoBecomeCreditStress ()

shortWindowVolDoesNotAutoEstablishStructuralRegime : SevenSessionVolImpliesStructuralRegimePermission → ⊥
shortWindowVolDoesNotAutoEstablishStructuralRegime ()

selectedFlipRateIsClosed : selectedBasketFlipRateClosed selectedAICapitalBasketResult ≡ true
selectedFlipRateIsClosed = refl

selectedVolatilityIsClosed : selectedBasketVolatilityClosed selectedAICapitalBasketResult ≡ true
selectedVolatilityIsClosed = refl

globalFlipRateStillOpen : globalAIMarketFlipRateClosed selectedAICapitalBasketResult ≡ false
globalFlipRateStillOpen = refl

globalVolatilityStillOpen : globalAIMarketVolatilityClosed selectedAICapitalBasketResult ≡ false
globalVolatilityStillOpen = refl
