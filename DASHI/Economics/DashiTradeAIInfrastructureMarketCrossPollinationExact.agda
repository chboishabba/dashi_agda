module DASHI.Economics.DashiTradeAIInfrastructureMarketCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Finance.DashiTradeFibreBridgeExact as TradeBridge
import DASHI.Trading.DashiTradeDreamOptionConeExact as Dream
import DASHI.Trading.TradingDeclaredRealizedViabilityBridgeExact as Viability
import DASHI.Economics.AICurrentRegimePromotionSchedulerExact as Promotion
import DASHI.Economics.AIEconomicUsefulWorkTimeSeriesExact as Useful

------------------------------------------------------------------------
-- DASHITRADE x AI INFRASTRUCTURE MARKET ECONOMICS
--
-- Structural reuse only.  A bullish signal or strong demand observation does
-- not create financing permission, refinancing capacity, executable liquidity
-- or realized capital viability.  Trading and AI infrastructure are not
-- identified as the same domain.
------------------------------------------------------------------------

data InfrastructureMarketSignal : Set where
  demandStrong
  utilisationHigh
  orderBacklogLarge
  acceleratorPricesFirm
  equityValuationsRising
  : InfrastructureMarketSignal

data InfrastructureAction : Set where
  financeNewCapacity
  refinanceExistingDebt
  holdCapacityFlat
  sellOrRetrenchCapacity
  : InfrastructureAction

data InfrastructureLiquidityState : Set where
  deepFundingMarket
  thinFundingMarket
  refinancingWindowClosed
  : InfrastructureLiquidityState

data InfrastructureCrowdingState : Set where
  uncrowdedBuildout
  crowdedSameThesisBuildout
  : InfrastructureCrowdingState

data InfrastructureUncertaintyState : Set where
  calibratedInfrastructureEconomics
  uncertainTerminalEconomics
  : InfrastructureUncertaintyState

data InfrastructureRiskState : Set where
  capitalRiskClear
  capitalRiskCaution
  capitalRiskBlocked
  : InfrastructureRiskState

record InfrastructureMarketFabric : Set where
  constructor infrastructureMarketFabric
  field
    signal : InfrastructureMarketSignal
    liquidity : InfrastructureLiquidityState
    crowding : InfrastructureCrowdingState
    uncertainty : InfrastructureUncertaintyState
    risk : InfrastructureRiskState
    terminalPayerReceiptReference : String

open InfrastructureMarketFabric public

-- Same bullish signal can sit inside very different financing fabrics.
cleanDemandState : InfrastructureMarketFabric
cleanDemandState = infrastructureMarketFabric
  demandStrong deepFundingMarket uncrowdedBuildout
  calibratedInfrastructureEconomics capitalRiskClear
  "terminal payer producer available in fixture"

crowdedDemandState : InfrastructureMarketFabric
crowdedDemandState = infrastructureMarketFabric
  demandStrong deepFundingMarket crowdedSameThesisBuildout
  uncertainTerminalEconomics capitalRiskCaution
  "terminal payer producer open in fixture"

sameDemandSignal : signal cleanDemandState ≡ signal crowdedDemandState
sameDemandSignal = refl

data RefinanceViability : Set where
  refinanceAvailable refinanceUnavailable : RefinanceViability

refinanceViability : InfrastructureMarketFabric → RefinanceViability
refinanceViability state with liquidity state
... | refinancingWindowClosed = refinanceUnavailable
... | thinFundingMarket = refinanceUnavailable
... | deepFundingMarket with crowding state
...   | crowdedSameThesisBuildout = refinanceUnavailable
...   | uncrowdedBuildout with uncertainty state
...     | uncertainTerminalEconomics = refinanceUnavailable
...     | calibratedInfrastructureEconomics with risk state
...       | capitalRiskBlocked = refinanceUnavailable
...       | _ = refinanceAvailable

sameDemandDifferentRefinanceViability :
  refinanceViability cleanDemandState ≡ refinanceViability crowdedDemandState → ⊥
sameDemandDifferentRefinanceViability ()

------------------------------------------------------------------------
-- dashiTRADE donor boundaries retained explicitly.
------------------------------------------------------------------------

tradeBoundary : TradeBridge.ResidualToTradeAuthorityBoundary
tradeBoundary = TradeBridge.canonicalResidualToTradeAuthorityBoundary

tradingDeclaredRealizedBoundary : Viability.TradingDeclaredRealizedBoundary
tradingDeclaredRealizedBoundary = Viability.canonicalTradingDeclaredRealizedBoundary

tradeHoldStillFirstClass :
  Dream.Available Dream.cleanLongState Dream.holdAction
tradeHoldStillFirstClass = Dream.holdAlwaysAvailable Dream.cleanLongState

------------------------------------------------------------------------
-- AI-infrastructure translation.
------------------------------------------------------------------------

record InfrastructureDecisionTrajectory : Set₁ where
  constructor infrastructureDecisionTrajectory
  field
    SignalState FinancingState ExecutionState RealizedState : Set
    signalState : SignalState
    financingState : FinancingState
    executionState : ExecutionState
    realizedState : RealizedState
    pathDependenceReceipt : Set

open InfrastructureDecisionTrajectory public

record InfrastructureTrajectoryCost : Set where
  constructor infrastructureTrajectoryCost
  field
    financingCost : String
    constructionCommitment : String
    refinancingExposure : String
    obsolescenceExposure : String
    optionalityLoss : String

open InfrastructureTrajectoryCost public

-- Equal endpoint capacity does not erase different financing/deployment paths.
data SameEndpointImpliesSameTrajectoryCostPermission : Set where

data DemandSignalImpliesFinancingPermission : Set where

data HighUtilisationImpliesRefinancingCapacityPermission : Set where

data RisingValuationImpliesRealizedInfrastructureViabilityPermission : Set where

data DeepLiquidityImpliesTerminalDemandPermission : Set where

data CrowdingImpliesFailurePermission : Set where

data TradeDomainEqualsAIInfrastructureDomainPermission : Set where

sameEndpointDoesNotAutoPromoteToSameTrajectoryCost :
  SameEndpointImpliesSameTrajectoryCostPermission → ⊥
sameEndpointDoesNotAutoPromoteToSameTrajectoryCost ()

demandSignalDoesNotAutoPromoteToFinancingPermission :
  DemandSignalImpliesFinancingPermission → ⊥
demandSignalDoesNotAutoPromoteToFinancingPermission ()

highUtilisationDoesNotAutoPromoteToRefinancingCapacity :
  HighUtilisationImpliesRefinancingCapacityPermission → ⊥
highUtilisationDoesNotAutoPromoteToRefinancingCapacity ()

risingValuationDoesNotAutoPromoteToRealizedInfrastructureViability :
  RisingValuationImpliesRealizedInfrastructureViabilityPermission → ⊥
risingValuationDoesNotAutoPromoteToRealizedInfrastructureViability ()

deepLiquidityDoesNotAutoPromoteToTerminalDemand :
  DeepLiquidityImpliesTerminalDemandPermission → ⊥
deepLiquidityDoesNotAutoPromoteToTerminalDemand ()

crowdingDoesNotAutoPromoteToFailure :
  CrowdingImpliesFailurePermission → ⊥
crowdingDoesNotAutoPromoteToFailure ()

tradeDomainDoesNotBecomeAIInfrastructureDomain :
  TradeDomainEqualsAIInfrastructureDomainPermission → ⊥
tradeDomainDoesNotBecomeAIInfrastructureDomain ()

------------------------------------------------------------------------
-- Promotion implications: refinancing and market-price signals need their own
-- producers, independent of the terminal economic validation producer.
------------------------------------------------------------------------

data InfrastructureMarketClaim : Set where
  refinancingWindowAdequate
  acceleratorSecondaryMarketLiquid
  marketPriceSupportsBookValue
  crowdedBuildoutStillFinanceable
  : InfrastructureMarketClaim

data InfrastructureMarketProducer : Set where
  refinancingSpreadAndCoverageProducer
  secondaryMarketDepthProducer
  marketToBookAndForcedSaleProducer
  crowdingFundingCapacityProducer
  : InfrastructureMarketProducer

requiredMarketProducer : InfrastructureMarketClaim → InfrastructureMarketProducer
requiredMarketProducer refinancingWindowAdequate = refinancingSpreadAndCoverageProducer
requiredMarketProducer acceleratorSecondaryMarketLiquid = secondaryMarketDepthProducer
requiredMarketProducer marketPriceSupportsBookValue = marketToBookAndForcedSaleProducer
requiredMarketProducer crowdedBuildoutStillFinanceable = crowdingFundingCapacityProducer

terminalPromotionStillSeparate :
  Promotion.CurrentEvidenceBundleImpliesTerminalValidationPermission → ⊥
terminalPromotionStillSeparate =
  Promotion.currentEvidenceBundleDoesNotCloseTerminalValidation

usageFutureClassStillSeparate :
  Useful.UsageGrowthDeterminesFutureClassPermission → ⊥
usageFutureClassStillSeparate = Useful.usageGrowthDoesNotDetermineFutureClass
