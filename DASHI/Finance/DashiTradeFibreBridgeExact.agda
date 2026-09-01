module DASHI.Finance.DashiTradeFibreBridgeExact where

open import DASHI.Core.Prelude

import DASHI.Finance.TemporalMarketFibreExact as Temporal
import DASHI.Finance.DeepStatArbFibrePipelineExact as StatArb
import DASHI.Trading.PermissionKernel as Legacy
import DASHI.Trading.DashiTradeDreamOptionConeExact as Dream
import DASHI.Trading.TradingDeclaredRealizedViabilityBridgeExact as Viability

------------------------------------------------------------------------
-- Quant-finance / dashiTRADE bridge.
--
-- A learned residual policy proposes direction/weights inside a market fibre.
-- Existing dashiTRADE owners retain authority over actionability.  Signal,
-- authorization, execution and realized viability remain distinct stages.
------------------------------------------------------------------------

record TradeSituatedFibre : Set where
  constructor tradeSituatedFibre
  field
    marketFibre : Temporal.MarketFibre
    residualFibre : StatArb.ResidualFibre
    tradeFabric : Dream.TradingFabricState
    legacyWindow : Legacy.MarketWindowState
    bridgeReceipt : String

open TradeSituatedFibre public

record ProposalAdapter : Set where
  constructor proposalAdapter
  field
    learnedPolicy : StatArb.LearnedPolicy
    proposedDirection : Dream.Direction
    proposalReceipt : String
    proposalCreatesAuthorization : Bool
    proposalCreatesAuthorizationIsFalse : proposalCreatesAuthorization ≡ false

open ProposalAdapter public

------------------------------------------------------------------------
-- Permission remains owned by the existing dashiTRADE kernels.
------------------------------------------------------------------------

legacyPermissionFor : TradeSituatedFibre → Legacy.Permission
legacyPermissionFor state = Legacy.authorize (Legacy.quotient (legacyWindow state))

optionConeAvailable :
  TradeSituatedFibre → Dream.TradeAction → Set
optionConeAvailable state action =
  Dream.Available (tradeFabric state) action

holdAlwaysAvailableInFibre :
  (state : TradeSituatedFibre) →
  optionConeAvailable state Dream.holdAction
holdAlwaysAvailableInFibre state =
  Dream.holdAlwaysAvailable (tradeFabric state)

------------------------------------------------------------------------
-- Same learned proposal can inhabit distinct situated trade fibres and have
-- different realized actionability.  This reuses the exact dashiTRADE witness.
------------------------------------------------------------------------

data CanonicalBridgeTag : Set where
  canonicalBridge : CanonicalBridgeTag

canonicalMarket : Temporal.MarketFibre
canonicalMarket = Temporal.fibre0

canonicalResidual : StatArb.ResidualFibre
canonicalResidual =
  StatArb.residualFibre
    0
    StatArb.pca
    "canonical residual payload"
    "canonical PIT factor-fit receipt"
    -- The universe field is structural here; the dedicated PIT owner proves
    -- admissibility of historical membership separately.
    (record
      { universeTime = 0
      ; constituentSet = "historical constituents at t0"
      ; membershipProvenance = "historical membership receipt"
      ; dynamicHistoricalPool = true
      })
    "canonical residual provenance"

cleanLongTradeFibre : TradeSituatedFibre
cleanLongTradeFibre =
  tradeSituatedFibre
    canonicalMarket
    canonicalResidual
    Dream.cleanLongState
    (Legacy.marketState Legacy.upward Legacy.calm Legacy.persistent Legacy.adequate Legacy.clear 0 0 0 Legacy.HOLD)
    "clean long bridge"

crowdedLongTradeFibre : TradeSituatedFibre
crowdedLongTradeFibre =
  tradeSituatedFibre
    canonicalMarket
    canonicalResidual
    Dream.crowdedLongState
    (Legacy.marketState Legacy.upward Legacy.calm Legacy.persistent Legacy.adequate Legacy.clear 0 0 0 Legacy.HOLD)
    "crowded long bridge"

sameResidualAcrossTradeFibres :
  residualFibre cleanLongTradeFibre ≡ residualFibre crowdedLongTradeFibre
sameResidualAcrossTradeFibres = refl

sameLongDirectionAcrossTradeFibres :
  Dream.candidateObserver (tradeFabric cleanLongTradeFibre)
  ≡ Dream.candidateObserver (tradeFabric crowdedLongTradeFibre)
sameLongDirectionAcrossTradeFibres = Dream.sameLongProposal

buyAvailabilityDiffersAcrossTradeFibres :
  Dream.actionAvailable (tradeFabric cleanLongTradeFibre) Dream.buyAction
  ≡ Dream.actionAvailable (tradeFabric crowdedLongTradeFibre) Dream.buyAction →
  ⊥
buyAvailabilityDiffersAcrossTradeFibres = Dream.buyAvailabilityDiffers

------------------------------------------------------------------------
-- Therefore residual/proposal equality cannot be promoted to trade equality.
------------------------------------------------------------------------

record ResidualToTradeAuthorityBoundary : Set where
  constructor residualToTradeAuthorityBoundary
  field
    sameResidualImpliesSameActionability : Bool
    sameResidualImpliesSameActionabilityIsFalse :
      sameResidualImpliesSameActionability ≡ false
    sameDirectionImpliesAuthorization : Bool
    sameDirectionImpliesAuthorizationIsFalse :
      sameDirectionImpliesAuthorization ≡ false
    holdIsFirstClass : Bool
    holdIsFirstClassIsTrue : holdIsFirstClass ≡ true

canonicalResidualToTradeAuthorityBoundary : ResidualToTradeAuthorityBoundary
canonicalResidualToTradeAuthorityBoundary =
  residualToTradeAuthorityBoundary false refl false refl true refl

------------------------------------------------------------------------
-- Trajectory-cost bridge.
--
-- The stat-arb execution fibre records realized cost/impact provenance; the
-- existing dashiTRADE owner additionally treats execution, risk, turnover and
-- future optionality loss as trajectory coordinates.  We preserve that richer
-- decomposition rather than collapsing everything into one scalar slippage.
------------------------------------------------------------------------

record FinanceTradeTrajectory : Set where
  constructor financeTradeTrajectory
  field
    execution : StatArb.ExecutionFibre
    tradeRoute : Dream.TradeRoute
    trajectoryCost : Dream.TrajectoryCost
    routeCostMatchesDream : trajectoryCost ≡ Dream.costFor tradeRoute
    trajectoryReceipt : String

open FinanceTradeTrajectory public

lowTurnoverTrajectory : StatArb.ExecutionFibre → FinanceTradeTrajectory
lowTurnoverTrajectory execution =
  financeTradeTrajectory
    execution
    Dream.lowTurnoverRoute
    (Dream.costFor Dream.lowTurnoverRoute)
    refl
    "finance execution mapped to dashiTRADE low-turnover trajectory"

churnTrajectory : StatArb.ExecutionFibre → FinanceTradeTrajectory
churnTrajectory execution =
  financeTradeTrajectory
    execution
    Dream.churnRoute
    (Dream.costFor Dream.churnRoute)
    refl
    "finance execution mapped to dashiTRADE churn trajectory"

sameEndpointDoesNotEraseTrajectoryCost :
  Dream.totalCost (trajectoryCost (lowTurnoverTrajectory
    (StatArb.executionFibre 1 "same fill" "cost" "impact" "receipt")))
  ≡
  Dream.totalCost (trajectoryCost (churnTrajectory
    (StatArb.executionFibre 1 "same fill" "cost" "impact" "receipt"))) →
  ⊥
sameEndpointDoesNotEraseTrajectoryCost =
  Dream.sameEndpointDifferentTrajectoryCost

------------------------------------------------------------------------
-- Declared/realized viability cross-pollination is preserved as a residual.
------------------------------------------------------------------------

cleanLongViabilityAligned :
  Viability.viabilityResidual
    Dream.longDirection
    (Dream.actionAvailable Dream.cleanLongState Dream.buyAction)
  ≡ Viability.proposalViabilityAligned
cleanLongViabilityAligned = refl

crowdedLongViabilityMismatch :
  Viability.viabilityResidual
    Dream.longDirection
    (Dream.actionAvailable Dream.crowdedLongState Dream.buyAction)
  ≡ Viability.proposalViabilityMismatch
crowdedLongViabilityMismatch = refl

bridgeBoundaryStatement : String
bridgeBoundaryStatement =
  "A factor-residual or learned-policy proposal is only a candidate direction inside a temporal market fibre. dashiTRADE permission, situated option-cone actionability, trajectory cost, and declared/realized viability remain independent proof-bearing stages before execution authority."
