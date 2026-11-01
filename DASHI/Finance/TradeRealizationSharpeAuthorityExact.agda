module DASHI.Finance.TradeRealizationSharpeAuthorityExact where

open import DASHI.Core.Prelude

import DASHI.Finance.DeepStatArbFibrePipelineExact as StatArb
import DASHI.Finance.DashiTradeFibreBridgeExact as Bridge
import DASHI.Trading.DashiTradeDreamOptionConeExact as Dream
import DASHI.Trading.TradingDeclaredRealizedViabilityBridgeExact as Viability

------------------------------------------------------------------------
-- BIDI terminal authority seam.
--
-- Walk backwards from a reported performance metric.  A metric is executable
-- evidence only if its return braid descends from realized trade viability and
-- a trajectory-cost-bearing execution path.  Proposal-only or endpoint-only
-- evidence cannot discharge those obligations.
------------------------------------------------------------------------

record ExecutableReturnReceipt : Set where
  constructor executableReturnReceipt
  field
    executionFibre : StatArb.ExecutionFibre
    returnFibre : StatArb.ReturnFibre
    tradeTrajectory : Bridge.FinanceTradeTrajectory
    realizedViability : Viability.ViabilityResidual
    actionWasViable : Bool
    actionWasViableIsTrue : actionWasViable ≡ true
    trajectoryCostRetained : Bool
    trajectoryCostRetainedIsTrue : trajectoryCostRetained ≡ true
    netReturnAfterTrajectoryCosts : Bool
    netReturnAfterTrajectoryCostsIsTrue : netReturnAfterTrajectoryCosts ≡ true

open ExecutableReturnReceipt public

record SharpeWithTradeAuthority : Set where
  constructor sharpeWithTradeAuthority
  field
    performance : StatArb.PerformanceContraction
    executionReceipt : ExecutableReturnReceipt
    performanceUsesRealizedNetReturns : Bool
    performanceUsesRealizedNetReturnsIsTrue :
      performanceUsesRealizedNetReturns ≡ true

open SharpeWithTradeAuthority public

------------------------------------------------------------------------
-- Missing viability/cost evidence remains a residual, not an automatic zero.
------------------------------------------------------------------------

data TradePerformanceResidual : Set where
  noTradeAuthority : TradePerformanceResidual
  proposalViabilityUnresolved : TradePerformanceResidual
  trajectoryCostUnresolved : TradePerformanceResidual
  executableNetReturnCertified : TradePerformanceResidual

classifyTradePerformance :
  Bool → Bool → Bool → TradePerformanceResidual
classifyTradePerformance false viability costs = noTradeAuthority
classifyTradePerformance true false costs = proposalViabilityUnresolved
classifyTradePerformance true true false = trajectoryCostUnresolved
classifyTradePerformance true true true = executableNetReturnCertified

unresolvedTrajectoryIsNotCertified :
  classifyTradePerformance true true false
  ≡ executableNetReturnCertified →
  ⊥
unresolvedTrajectoryIsNotCertified ()

proposalOnlyIsNotCertified :
  classifyTradePerformance false true true
  ≡ executableNetReturnCertified →
  ⊥
proposalOnlyIsNotCertified ()

------------------------------------------------------------------------
-- Existing dashiTRADE trajectory distinction survives metric aggregation.
------------------------------------------------------------------------

record MetricTrajectoryBoundary : Set where
  constructor metricTrajectoryBoundary
  field
    sameEndpointImpliesSameTradeCost : Bool
    sameEndpointImpliesSameTradeCostIsFalse :
      sameEndpointImpliesSameTradeCost ≡ false
    sameSignalImpliesSameRealizedViability : Bool
    sameSignalImpliesSameRealizedViabilityIsFalse :
      sameSignalImpliesSameRealizedViability ≡ false
    reportedSharpeCreatesTradePermission : Bool
    reportedSharpeCreatesTradePermissionIsFalse :
      reportedSharpeCreatesTradePermission ≡ false

canonicalMetricTrajectoryBoundary : MetricTrajectoryBoundary
canonicalMetricTrajectoryBoundary =
  metricTrajectoryBoundary false refl false refl false refl

------------------------------------------------------------------------
-- Concrete cost witness from the existing option-cone owner.
------------------------------------------------------------------------

lowRouteCost : Nat
lowRouteCost = Dream.totalCost (Dream.costFor Dream.lowTurnoverRoute)

churnRouteCost : Nat
churnRouteCost = Dream.totalCost (Dream.costFor Dream.churnRoute)

lowAndChurnCostsDiffer : lowRouteCost ≡ churnRouteCost → ⊥
lowAndChurnCostsDiffer = Dream.sameEndpointDifferentTrajectoryCost

terminalAuthorityStatement : String
terminalAuthorityStatement =
  "A reported Sharpe is terminal evidence only after the return braid is backed by realized dashiTRADE viability, execution provenance and retained trajectory costs. Signal equality, endpoint equality and proposal direction do not discharge those obligations."
