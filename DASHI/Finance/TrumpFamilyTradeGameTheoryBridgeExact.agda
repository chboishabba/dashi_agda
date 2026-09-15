module DASHI.Finance.TrumpFamilyTradeGameTheoryBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Finance.TrumpFamilyTradeSourceAtlasExact as Atlas
import DASHI.Finance.TrumpFamilyTradePNFBridgeExact as PNF
import DASHI.Finance.DashiTradeFibreBridgeExact as DashiTrade
import DASHI.GameTheory.StrategicInteractionCoreExact as Game
import DASHI.GameTheory.SourceConditionedMarketInformationExact as Information
import DASHI.GameTheory.RepeatedStrategicLearningMemoryBridgeExact as Repeated

------------------------------------------------------------------------
-- TRUMP-FAMILY TRADE / STRATEGIC-INFORMATION BRIDGE
--
-- The source atlas can parameterise information-state and repeated-history
-- models, but source evidence does not become a strategy, trade signal or
-- equilibrium witness.  dashiTRADE remains the execution/actionability owner.
------------------------------------------------------------------------

record SourceBackedMarketEvent : Set₁ where
  constructor source-backed-market-event
  field
    claim : Atlas.TradeEvidenceClaim
    pnf : PNF.TradeClaimPNFBinding claim
    publicInformationReference : String
    nonpublicInformationEstablished : Bool
    nonpublicInformationEstablishedIsFalse :
      nonpublicInformationEstablished ≡ false

open SourceBackedMarketEvent public

record MarketTimingEdge : Set₁ where
  constructor market-timing-edge
  field
    earlier later : SourceBackedMarketEvent
    orderingReference : String
    causalEffectEstablished : Bool
    causalEffectEstablishedIsFalse : causalEffectEstablished ≡ false
    hiddenKnowledgeEstablished : Bool
    hiddenKnowledgeEstablishedIsFalse : hiddenKnowledgeEstablished ≡ false

open MarketTimingEdge public

------------------------------------------------------------------------
-- Truth API is especially useful as an information-structure example.  The
-- primary issuer source states low-latency access to public posts and a target
-- customer class including HFT/algorithmic firms.  That can support a timing or
-- information-access model.  It does not establish MNPI, insider trading or a
-- profitable strategy.
------------------------------------------------------------------------

truthAPIClaim : Atlas.TradeEvidenceClaim
truthAPIClaim = Atlas.truthAPIPrimary

truthAPIIsPrimaryPaid : Atlas.primarySourcePaid truthAPIClaim ≡ true
truthAPIIsPrimaryPaid = refl

record PaidLatencyInformationSurface : Set where
  constructor paid-latency-information-surface
  field
    sourceClaim : Atlas.TradeEvidenceClaim
    dataIsDescribedAsPublic : Bool
    latencyAdvantageDescribed : Bool
    institutionalTradingUseDescribed : Bool
    materialNonpublicInformationProved : Bool
    profitableTradingStrategyProved : Bool

canonicalTruthAPISurface : PaidLatencyInformationSurface
canonicalTruthAPISurface =
  paid-latency-information-surface
    truthAPIClaim true true true false false

------------------------------------------------------------------------
-- Explicit dashiTRADE authority separation.
------------------------------------------------------------------------

record EvidenceTradeAuthorityBoundary : Set₁ where
  constructor evidence-trade-authority-boundary
  field
    evidenceClaim : Atlas.TradeEvidenceClaim
    tradeState : DashiTrade.TradeSituatedFibre
    sourceEvidenceCreatesPermission : Bool
    sourceEvidenceCreatesPermissionIsFalse :
      sourceEvidenceCreatesPermission ≡ false
    timingEdgeCreatesPermission : Bool
    timingEdgeCreatesPermissionIsFalse :
      timingEdgeCreatesPermission ≡ false
    dashiTradeBoundary : DashiTrade.ResidualToTradeAuthorityBoundary

open EvidenceTradeAuthorityBoundary public

canonicalEvidenceTradeBoundary : EvidenceTradeAuthorityBoundary
canonicalEvidenceTradeBoundary =
  evidence-trade-authority-boundary
    Atlas.donJrTMTGRSU
    DashiTrade.cleanLongTradeFibre
    false refl
    false refl
    DashiTrade.canonicalResidualToTradeAuthorityBoundary

------------------------------------------------------------------------
-- Repeated-game / memory hook.  The actual repeated process remains supplied by
-- the canonical game owner.  This bridge merely records that a source-backed
-- event may be bound to a history element; it does not infer best response,
-- motive or equilibrium from the event.
------------------------------------------------------------------------

record SourceBackedRepeatedHistory
    {G : Game.StrategicGame}
    (R : Repeated.RepeatedStrategicLearningProcess G) : Set₁ where
  constructor source-backed-repeated-history
  field
    EventIndex : Set
    eventAt : EventIndex → SourceBackedMarketEvent
    timeAt : EventIndex → Repeated.Time R
    historyBindingReference : EventIndex → String

open SourceBackedRepeatedHistory public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data TradeTimingMeansInsiderTradingPermission : Set where
data FamilyOwnershipMeansSharedPrivateInformationPermission : Set where
data PublicSignalMeansTradeRecommendationPermission : Set where
data RepeatedHistoryMeansBestResponsePermission : Set where
data RegulatoryConcernMeansViolationPermission : Set where

tradeTimingDoesNotProveInsiderTrading : TradeTimingMeansInsiderTradingPermission → ⊥
tradeTimingDoesNotProveInsiderTrading ()

familyOwnershipDoesNotProveSharedPrivateInformation :
  FamilyOwnershipMeansSharedPrivateInformationPermission → ⊥
familyOwnershipDoesNotProveSharedPrivateInformation ()

publicSignalDoesNotCreateTradeRecommendation : PublicSignalMeansTradeRecommendationPermission → ⊥
publicSignalDoesNotCreateTradeRecommendation ()

repeatedHistoryDoesNotCreateBestResponse : RepeatedHistoryMeansBestResponsePermission → ⊥
repeatedHistoryDoesNotCreateBestResponse ()

regulatoryConcernDoesNotCreateViolation : RegulatoryConcernMeansViolationPermission → ⊥
regulatoryConcernDoesNotCreateViolation ()

record TrumpFamilyTradeGameTheoryBoundary : Set where
  constructor trump-family-trade-game-theory-boundary
  field
    sourceEvidenceCanParameteriseInformationState : Bool
    publicSignalAndFineEvidenceRemainSeparate : Bool
    tradeTimingDoesNotProveInsiderTrading : Bool
    familyRelationDoesNotTransportKnowledge : Bool
    truthAPIPrimarySourceDoesNotProveMNPI : Bool
    gameCompatibilityDoesNotRevealMotive : Bool
    dashiTradeRetainsExecutionAuthority : Bool

canonicalTrumpFamilyTradeGameTheoryBoundary : TrumpFamilyTradeGameTheoryBoundary
canonicalTrumpFamilyTradeGameTheoryBoundary =
  trump-family-trade-game-theory-boundary true true true true true true true
