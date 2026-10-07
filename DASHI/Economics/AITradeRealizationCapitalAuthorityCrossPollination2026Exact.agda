module DASHI.Economics.AITradeRealizationCapitalAuthorityCrossPollination2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Finance.DashiTradeFibreBridgeExact as TradeBridge
import DASHI.Finance.TradeRealizationSharpeAuthorityExact as TradeAuthority
import DASHI.Economics.AIOpenClosedGrowthCapitalRecoveryExact as Growth
import DASHI.Economics.AITerminalPayerEconomicValidationExact as Terminal
import DASHI.Economics.DashiTradeAICapitalStressRuntimeCrossPollination2026Exact as Runtime

------------------------------------------------------------------------
-- TRADE REALISATION AUTHORITY -> AI CAPITAL REALISATION AUTHORITY
--
-- dashiTRADE distinguishes proposal/performance metrics from realized net
-- returns after viability and trajectory costs.  The AI-capital analogue is:
-- reported revenue, EBITDA, utilisation, backlog or valuation are intermediate
-- metrics until the capital trajectory retains funding, depreciation,
-- replacement-capex, obsolescence and terminal-payer obligations.
------------------------------------------------------------------------

data AICapitalPerformanceResidual : Set where
  noTerminalPayerAuthority : AICapitalPerformanceResidual
  fundingCostUnresolved : AICapitalPerformanceResidual
  depreciationOrReplacementUnresolved : AICapitalPerformanceResidual
  obsolescenceResidual : AICapitalPerformanceResidual
  realizedCapitalRecoveryCertified : AICapitalPerformanceResidual

classifyAICapitalPerformance :
  Bool → Bool → Bool → Bool → AICapitalPerformanceResidual
classifyAICapitalPerformance false funding replacement obsolescence =
  noTerminalPayerAuthority
classifyAICapitalPerformance true false replacement obsolescence =
  fundingCostUnresolved
classifyAICapitalPerformance true true false obsolescence =
  depreciationOrReplacementUnresolved
classifyAICapitalPerformance true true true false = obsolescenceResidual
classifyAICapitalPerformance true true true true =
  realizedCapitalRecoveryCertified

noTerminalPayerIsNotCertified :
  classifyAICapitalPerformance false true true true
  ≡ realizedCapitalRecoveryCertified → ⊥
noTerminalPayerIsNotCertified ()

fundingResidualIsNotCertified :
  classifyAICapitalPerformance true false true true
  ≡ realizedCapitalRecoveryCertified → ⊥
fundingResidualIsNotCertified ()

replacementResidualIsNotCertified :
  classifyAICapitalPerformance true true false true
  ≡ realizedCapitalRecoveryCertified → ⊥
replacementResidualIsNotCertified ()

obsolescenceResidualIsNotCertified :
  classifyAICapitalPerformance true true true false
  ≡ realizedCapitalRecoveryCertified → ⊥
obsolescenceResidualIsNotCertified ()

data ReportedRevenueImpliesCapitalAuthorityPermission : Set where
data ReportedEBITDAImpliesCapitalAuthorityPermission : Set where
data ReportedValuationImpliesCapitalAuthorityPermission : Set where
data BacklogImpliesCapitalAuthorityPermission : Set where

reportedRevenueDoesNotAutoCreateCapitalAuthority :
  ReportedRevenueImpliesCapitalAuthorityPermission → ⊥
reportedRevenueDoesNotAutoCreateCapitalAuthority ()

reportedEBITDADoesNotAutoCreateCapitalAuthority :
  ReportedEBITDAImpliesCapitalAuthorityPermission → ⊥
reportedEBITDADoesNotAutoCreateCapitalAuthority ()

reportedValuationDoesNotAutoCreateCapitalAuthority :
  ReportedValuationImpliesCapitalAuthorityPermission → ⊥
reportedValuationDoesNotAutoCreateCapitalAuthority ()

backlogDoesNotAutoCreateCapitalAuthority :
  BacklogImpliesCapitalAuthorityPermission → ⊥
backlogDoesNotAutoCreateCapitalAuthority ()

tradeMetricBoundary : TradeAuthority.MetricTrajectoryBoundary
tradeMetricBoundary = TradeAuthority.canonicalMetricTrajectoryBoundary

tradeAuthorityBoundary : TradeBridge.ResidualToTradeAuthorityBoundary
tradeAuthorityBoundary = TradeBridge.canonicalResidualToTradeAuthorityBoundary

capitalCrackSpreadSurface : Set₁
capitalCrackSpreadSurface = Growth.CapitalRecoveryRequirement

terminalSignalFirewall :
  Terminal.SurroundingSignalsImplyEconomicValidationPermission → ⊥
terminalSignalFirewall = Terminal.surroundingSignalsDoNotAutoPromoteToEconomicValidation

runtimeBoundaryStatement : String
runtimeBoundaryStatement =
  "The dashiTRADE terminal-authority seam survives cross-pollination: AI revenue, EBITDA, backlog, utilisation and valuation remain pre-terminal metrics until external payer, funding-cost, depreciation/replacement and obsolescence obligations are discharged."

runtimeStateStillSeparate : Runtime.RuntimeObservedAIState
runtimeStateStillSeparate = Runtime.candidateOctober2026RuntimeState
