module DASHI.Finance.TrumpTariffDashiTradeBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Finance.DashiTradeFibreBridgeExact as DashiTrade
import DASHI.Finance.TrumpTariffMarketSignalSourceExact as SourceAtlas
import DASHI.Finance.TrumpTradeDecisionProvenanceExact as Decision
import DASHI.Trading.DashiTradeDreamOptionConeExact as Dream

record TariffTradeEvidenceState : Set₁ where
  constructor tariff-trade-evidence-state
  field
    publicSequence : SourceAtlas.PublicSequence
    decisionProvenance : Decision.TradeDecisionProvenance
    situatedTrade : DashiTrade.TradeSituatedFibre
    evidenceReference : String
open TariffTradeEvidenceState public

canonicalTariffTradeEvidenceState : TariffTradeEvidenceState
canonicalTariffTradeEvidenceState = tariff-trade-evidence-state
  SourceAtlas.canonicalApril9Sequence Decision.coinbaseDecisionProvenance
  DashiTrade.cleanLongTradeFibre
  "illustrative authority-boundary carrier only; the 2025 tariff sequence and 2026 Coinbase event are not asserted to be one trade history"

record TariffTradeAuthorityBoundary : Set₁ where
  constructor tariff-trade-authority-boundary
  field
    state : TariffTradeEvidenceState
    publicSignalCreatesAuthorization : Bool
    publicSignalCreatesAuthorizationIsFalse : publicSignalCreatesAuthorization ≡ false
    marketMoveCreatesDirection : Bool
    marketMoveCreatesDirectionIsFalse : marketMoveCreatesDirection ≡ false
    disclosedTradeCreatesRecommendation : Bool
    disclosedTradeCreatesRecommendationIsFalse : disclosedTradeCreatesRecommendation ≡ false
    investigationRequestCreatesRecommendation : Bool
    investigationRequestCreatesRecommendationIsFalse : investigationRequestCreatesRecommendation ≡ false
    canonicalTradeAuthority : DashiTrade.ResidualToTradeAuthorityBoundary
open TariffTradeAuthorityBoundary public

canonicalTariffTradeAuthorityBoundary : TariffTradeAuthorityBoundary
canonicalTariffTradeAuthorityBoundary = tariff-trade-authority-boundary canonicalTariffTradeEvidenceState false refl false refl false refl false refl DashiTrade.canonicalResidualToTradeAuthorityBoundary

holdRemainsAvailable : DashiTrade.optionConeAvailable (situatedTrade canonicalTariffTradeEvidenceState) Dream.holdAction
holdRemainsAvailable = DashiTrade.holdAlwaysAvailableInFibre (situatedTrade canonicalTariffTradeEvidenceState)

data PublicSignalAutomaticallyMeansBuy : Set where
data HistoricMarketRallyAutomaticallyMeansExAnteAlpha : Set where
data DisclosedPoliticalTradeAutomaticallyMeansCopyTrade : Set where
data InvestigationRequestAutomaticallyMeansShort : Set where
publicSignalDoesNotMeanBuy : PublicSignalAutomaticallyMeansBuy → ⊥
publicSignalDoesNotMeanBuy ()
historicRallyDoesNotCreateExAnteAlpha : HistoricMarketRallyAutomaticallyMeansExAnteAlpha → ⊥
historicRallyDoesNotCreateExAnteAlpha ()
disclosedTradeDoesNotCreateCopyTrade : DisclosedPoliticalTradeAutomaticallyMeansCopyTrade → ⊥
disclosedTradeDoesNotCreateCopyTrade ()
investigationRequestDoesNotMeanShort : InvestigationRequestAutomaticallyMeansShort → ⊥
investigationRequestDoesNotMeanShort ()
