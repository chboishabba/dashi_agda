module DASHI.Economics.DashiTradeAICapitalStressRuntimeCrossPollination2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.DashiTradeAIInfrastructureMarketCrossPollinationExact as TradeAI
import DASHI.Economics.AICapitalRecoveryEntanglement2026Exact as Capital
import DASHI.Economics.AIGeometricMarketStressOperator2026Exact as Geometry
import DASHI.Economics.AIEnergyInfrastructureFundingStress2026Exact as Funding

------------------------------------------------------------------------
-- DASHITRADE RUNTIME -> AI CAPITAL-RECOVERY
--
-- Structural reuse only: dashiTRADE rejects apparent edge that does not
-- survive boundary costs / persistence / robustness.  For AI infrastructure,
-- revenue, capability and utilisation are therefore pre-boundary signals;
-- funding, depreciation, replacement capex, rollover, obsolescence and
-- terminal-payer quality remain separate recovery boundaries.
------------------------------------------------------------------------

primaryCodeCarrierKind : Source.SourceKind
primaryCodeCarrierKind = Source.namedSourceKind "primary repository code carrier"

primaryNormativeDocKind : Source.SourceKind
primaryNormativeDocKind = Source.namedSourceKind "primary repository normative document"

dashiTradeRuntimeSource : Source.AttributedSource
dashiTradeRuntimeSource = Source.mkNoDOISource
  "Johl Brown / dashiTRADE"
  "dashiTRADE runtime"
  "GitHub repository"
  "2026"
  "https://github.com/chboishabba/dashiTRADE"
  primaryCodeCarrierKind
  "source carrier for regime, structural-stress, Phase-9 expected-surplus/cost-survival, capital-ledger and proof-receipt machinery; no trading authority imported"
  Source.publicAttribution

dashiTradeBoundaryStableEigenSource : Source.AttributedSource
dashiTradeBoundaryStableEigenSource = Source.mkNoDOISource
  "Johl Brown / dashiTRADE"
  "Boundary-Stable Eigen-Events (Normative Definition)"
  "dashiTRADE docs/boundary_stable_eigen.md"
  "2026"
  "https://github.com/chboishabba/dashiTRADE/blob/main/docs/boundary_stable_eigen.md"
  primaryNormativeDocKind
  "source for the invariant that apparent edge is inadmissible unless it survives boundary costs, persistence and robustness"
  Source.publicAttribution

reutersAICreditSpread2026 : Source.AttributedSource
reutersAICreditSpread2026 = Source.mkNoDOISource
  "Reuters"
  "Corporate bond buyers get picky with flood of AI debt"
  "Reuters"
  "2026-09-22"
  "https://www.reuters.com/legal/transactional/corporate-bond-buyers-get-picky-with-flood-ai-debt-2026-09-22/"
  Source.newsSource
  "secondary carrier for approximately 115 bp AI-related investment-grade spreads versus 78 bp broader investment-grade spreads and projected hyperscaler issuance pressure"
  Source.publicAttribution

reutersNvidiaCollateral2026 : Source.AttributedSource
reutersNvidiaCollateral2026 = Source.mkNoDOISource
  "Reuters"
  "Nvidia's bet that its chips can finance the AI boom gets a Wall Street reality check"
  "Reuters"
  "2026-10-01"
  "https://www.reuters.com/legal/transactional/nvidias-bet-that-its-chips-can-finance-ai-boom-gets-wall-street-reality-check-2026-10-01/"
  Source.newsSource
  "secondary carrier for lender skepticism toward chip collateral and a reported 3-4 year lender depreciation framing versus Nvidia's longer useful-life framing"
  Source.publicAttribution

reutersSpaceXApollo2026 : Source.AttributedSource
reutersSpaceXApollo2026 = Source.mkNoDOISource
  "Reuters"
  "SpaceX seeks $40 billion financing led by Apollo to buy Nvidia chips, FT reports"
  "Reuters"
  "2026-10-06"
  "https://www.reuters.com/business/media-telecom/spacex-seeks-40-billion-buy-nvidia-chips-ft-reports-2026-10-06/"
  Source.newsSource
  "secondary carrier for a reported USD 40 billion financing proposal and the quoted USD 1.5 trillion external AI-infrastructure finance estimate through 2028"
  Source.publicAttribution

------------------------------------------------------------------------
-- Runtime-parity state.
------------------------------------------------------------------------

data RuntimeCapitalRegime : Set where
  clean caution stressed dislocation backstopMasked : RuntimeCapitalRegime

record RuntimeMarketTelemetry : Set where
  constructor runtimeMarketTelemetry
  field
    creditSpreadStress priceStress volatilityStress regimeFlipStress : Trit

record CommercialBoundaryState : Set where
  constructor commercialBoundaryState
  field
    terminalPayerAdequacy internalCyclePressure supplierFinancedDemand
      customerConcentration capitalSpread scarcityRentSpread
      capabilitySubstitutionPressure fundingPressure rolloverPressure : Trit

record RuntimeObservedAIState : Set where
  constructor runtimeObservedAIState
  field
    market : RuntimeMarketTelemetry
    commercial : CommercialBoundaryState
    policyBackstopSalience : Trit
    regime : RuntimeCapitalRegime

candidateOctober2026RuntimeState : RuntimeObservedAIState
candidateOctober2026RuntimeState = runtimeObservedAIState
  (runtimeMarketTelemetry pos pos pos pos)
  (commercialBoundaryState neg pos pos pos neg neg pos pos pos)
  pos stressed

------------------------------------------------------------------------
-- Boundary-stable capital recovery.
------------------------------------------------------------------------

record BoundaryStableCapitalRecovery : Set₁ where
  field
    GrossEconomicEdge BoundaryCost Persistence Robustness TerminalValidation : Set
    grossEconomicEdge : GrossEconomicEdge
    boundaryCost : BoundaryCost
    persistence : Persistence
    robustness : Robustness
    terminalValidation : TerminalValidation

data GrossRevenueImpliesBoundaryStableRecoveryPermission : Set where
data CapabilityGrowthImpliesBoundaryStableRecoveryPermission : Set where
data HighUtilisationImpliesBoundaryStableRecoveryPermission : Set where

grossRevenueDoesNotAutoCloseBoundaryStableRecovery :
  GrossRevenueImpliesBoundaryStableRecoveryPermission → ⊥
grossRevenueDoesNotAutoCloseBoundaryStableRecovery ()

capabilityGrowthDoesNotAutoCloseBoundaryStableRecovery :
  CapabilityGrowthImpliesBoundaryStableRecoveryPermission → ⊥
capabilityGrowthDoesNotAutoCloseBoundaryStableRecovery ()

highUtilisationDoesNotAutoCloseBoundaryStableRecovery :
  HighUtilisationImpliesBoundaryStableRecoveryPermission → ⊥
highUtilisationDoesNotAutoCloseBoundaryStableRecovery ()

------------------------------------------------------------------------
-- Market tape != fundamentals.
------------------------------------------------------------------------

data CalmMarketImpliesCommercialViabilityPermission : Set where
data RisingEquityPriceImpliesCapitalRecoveryPermission : Set where
data CreditSpreadWideningImpliesInsolvencyPermission : Set where
data PolicyBackstopImpliesTerminalPayerPermission : Set where

calmMarketDoesNotAutoCloseCommercialViability :
  CalmMarketImpliesCommercialViabilityPermission → ⊥
calmMarketDoesNotAutoCloseCommercialViability ()

risingEquityPriceDoesNotAutoCloseCapitalRecovery :
  RisingEquityPriceImpliesCapitalRecoveryPermission → ⊥
risingEquityPriceDoesNotAutoCloseCapitalRecovery ()

creditSpreadWideningDoesNotAutoProveInsolvency :
  CreditSpreadWideningImpliesInsolvencyPermission → ⊥
creditSpreadWideningDoesNotAutoProveInsolvency ()

policyBackstopDoesNotAutoManufactureTerminalPayer :
  PolicyBackstopImpliesTerminalPayerPermission → ⊥
policyBackstopDoesNotAutoManufactureTerminalPayer ()

record MarketStressObservation : Set where
  constructor marketStressObservation
  field
    reading : String
    source : Source.AttributedSource
    supportsFundingStressCoordinate provesDefault provesBubble : Bool

aiCreditSpreadPremium20260922 : MarketStressObservation
aiCreditSpreadPremium20260922 = marketStressObservation
  "AI-related IG spreads were reported around 115 bp versus 78 bp broad IG; relative funding stress is supported, default is not."
  reutersAICreditSpread2026 true false false

chipCollateralDurationMismatch20261001 : MarketStressObservation
chipCollateralDurationMismatch20261001 = marketStressObservation
  "Reported lender depreciation assumptions were materially shorter than Nvidia's longer useful-life framing, preserving collateral-duration risk."
  reutersNvidiaCollateral2026 true false false

externalFinanceScale20261006 : MarketStressObservation
externalFinanceScale20261006 = marketStressObservation
  "A reported USD 40 billion SpaceX/Apollo proposal plus a quoted USD 1.5 trillion external-finance estimate supports a large future capital-requirement coordinate."
  reutersSpaceXApollo2026 true false false

tradeCrowdingBoundary : TradeAI.InfrastructureMarketFabric
tradeCrowdingBoundary = TradeAI.crowdedDemandState

capitalEntanglementBoundary : Capital.TwoGeometryCapitalRecoveryState
capitalEntanglementBoundary = Capital.candidateTwoGeometryState2026

geometricStressBoundary : Geometry.QualitativeJointStress
geometricStressBoundary = Geometry.candidateOctober2026JointStress

fundingClockBoundary : Funding.FundingClock
fundingClockBoundary = Funding.candidateBurryStyleFundingClock

data DashiTradeRuntimeImpliesTradingSignalPermission : Set where
data MarketStressImpliesBubblePermission : Set where
data BackstopMaskedImpliesRegulatoryCapturePermission : Set where

dashiTradeCrossPollinationDoesNotCreateTradingSignal :
  DashiTradeRuntimeImpliesTradingSignalPermission → ⊥
dashiTradeCrossPollinationDoesNotCreateTradingSignal ()

marketStressDoesNotAutoProveBubble : MarketStressImpliesBubblePermission → ⊥
marketStressDoesNotAutoProveBubble ()

backstopMaskedDoesNotAutoProveRegulatoryCapture :
  BackstopMaskedImpliesRegulatoryCapturePermission → ⊥
backstopMaskedDoesNotAutoProveRegulatoryCapture ()
