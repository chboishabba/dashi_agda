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
------------------------------------------------------------------------

data AICapitalPerformanceResidual : Set where
  runtimeParityUnresolved : AICapitalPerformanceResidual
  noTerminalPayerAuthority : AICapitalPerformanceResidual
  fundingCostUnresolved : AICapitalPerformanceResidual
  depreciationOrReplacementUnresolved : AICapitalPerformanceResidual
  rolloverOrRefinancingUnresolved : AICapitalPerformanceResidual
  obsolescenceResidual : AICapitalPerformanceResidual
  persistenceOrRobustnessUnresolved : AICapitalPerformanceResidual
  realizedCapitalRecoveryCertified : AICapitalPerformanceResidual

-- Legacy four-boundary surface retained for existing consumers.
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

-- Exact max-cut surface.  No runtime state can enter the economic ladder until
-- same-object parity is established.  Rollover/refinancing and persistence are
-- explicit rungs rather than being silently absorbed into another label.
classifyAICapitalPerformanceMaxCut :
  Bool → Bool → Bool → Bool → Bool → Bool → Bool → AICapitalPerformanceResidual
classifyAICapitalPerformanceMaxCut false terminal funding replacement rollover obsolescence persistence =
  runtimeParityUnresolved
classifyAICapitalPerformanceMaxCut true false funding replacement rollover obsolescence persistence =
  noTerminalPayerAuthority
classifyAICapitalPerformanceMaxCut true true false replacement rollover obsolescence persistence =
  fundingCostUnresolved
classifyAICapitalPerformanceMaxCut true true true false rollover obsolescence persistence =
  depreciationOrReplacementUnresolved
classifyAICapitalPerformanceMaxCut true true true true false obsolescence persistence =
  rolloverOrRefinancingUnresolved
classifyAICapitalPerformanceMaxCut true true true true true false persistence =
  obsolescenceResidual
classifyAICapitalPerformanceMaxCut true true true true true true false =
  persistenceOrRobustnessUnresolved
classifyAICapitalPerformanceMaxCut true true true true true true true =
  realizedCapitalRecoveryCertified

runtimeParityResidualIsNotCertified :
  classifyAICapitalPerformanceMaxCut false true true true true true true
  ≡ realizedCapitalRecoveryCertified → ⊥
runtimeParityResidualIsNotCertified ()

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

rolloverResidualIsNotCertified :
  classifyAICapitalPerformanceMaxCut true true true true false true true
  ≡ realizedCapitalRecoveryCertified → ⊥
rolloverResidualIsNotCertified ()

obsolescenceResidualIsNotCertified :
  classifyAICapitalPerformance true true true false
  ≡ realizedCapitalRecoveryCertified → ⊥
obsolescenceResidualIsNotCertified ()

persistenceResidualIsNotCertified :
  classifyAICapitalPerformanceMaxCut true true true true true true false
  ≡ realizedCapitalRecoveryCertified → ⊥
persistenceResidualIsNotCertified ()

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
  "The dashiTRADE terminal-authority seam survives cross-pollination: AI revenue, EBITDA, backlog, utilisation and valuation remain pre-terminal metrics until same-object parity, external payer, funding-cost, depreciation/replacement, rollover/refinancing, obsolescence and persistence obligations are discharged."

runtimeStateStillSeparate : Runtime.RuntimeObservedAIState
runtimeStateStillSeparate = Runtime.candidateOctober2026RuntimeState
