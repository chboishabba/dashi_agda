module DASHI.Economics.AnthropicProspectusCapitalRecovery2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Economics.AICapitalRecoveryEntanglement2026Exact as Capital
import DASHI.Economics.AIOpenClosedGrowthCapitalRecoveryExact as Growth
import DASHI.Economics.AITerminalPayerEconomicValidationExact as Terminal

------------------------------------------------------------------------
-- ANTHROPIC PROSPECTUS / CAPITAL-RECOVERY CALIBRATION
--
-- Monetary values are stored as source-bounded readings rather than promoted
-- to mathematical facts about future viability.  The operating-loss reading
-- is kept distinct from the much larger GAAP net loss because financing-
-- instrument accounting contributes materially to the latter.
------------------------------------------------------------------------

reutersS1QA2026 : Source.AttributedSource
reutersS1QA2026 = Source.mkNoDOISource
  "Reuters"
  "Inside Anthropic's confidential S-1: a Q&A"
  "Reuters"
  "2026-09-30"
  "https://www.reuters.com/technology/artificial-intelligence/inside-anthropics-confidential-s-1-qa-2026-09-30/"
  Source.newsSource
  "secondary carrier for the prospectus distinction between operating losses and financing-accounting losses, and for cloud-partner revenue dependence"
  Source.publicAttribution

reutersBroadcomLoan2026 : Source.AttributedSource
reutersBroadcomLoan2026 = Source.mkNoDOISource
  "Reuters"
  "Broadcom to lend Anthropic up to $42 billion to lease its chips, filing says"
  "Reuters"
  "2026-10-01"
  "https://www.reuters.com/business/broadcom-lend-anthropic-up-42-billion-lease-its-chips-filing-says-2026-10-01/"
  Source.newsSource
  "secondary carrier for a supplier-linked financing arrangement: up to USD 42 billion of financing associated with a five-year USD 125.2 billion capacity commitment, including a convertible instrument"
  Source.publicAttribution

reutersAnthropicTrajectory2026 : Source.AttributedSource
reutersAnthropicTrajectory2026 = Source.mkNoDOISource
  "Reuters"
  "Anthropic's path from AI startup to industry-defining IPO"
  "Reuters"
  "2026-09-28"
  "https://www.reuters.com/technology/anthropics-path-ai-startup-industry-defining-ipo-2026-09-28/"
  Source.newsSource
  "secondary carrier for the reported 2028 revenue projection of roughly USD 190-200 billion and the contemporaneous revenue-run-rate trajectory"
  Source.publicAttribution

record ProspectusReading : Set where
  constructor prospectusReading
  field
    metric : String
    reading : String
    source : Source.AttributedSource
    cashOperatingMetric : Bool
    forecast : Bool

open ProspectusReading public

operatingLossReading : ProspectusReading
operatingLossReading = prospectusReading
  "2025 operating loss"
  "more than USD 8 billion; kept separate from the roughly USD 42 billion GAAP net loss"
  reutersS1QA2026 true false

financingAccountingReading : ProspectusReading
financingAccountingReading = prospectusReading
  "2025 financing-accounting contribution"
  "roughly USD 34 billion of the reported net loss was associated with financing-instrument accounting effects"
  reutersS1QA2026 false false

futureRevenueProjectionReading : ProspectusReading
futureRevenueProjectionReading = prospectusReading
  "2028 revenue projection"
  "roughly USD 190-200 billion"
  reutersAnthropicTrajectory2026 false true

broadcomSupplierFinancingReading : ProspectusReading
broadcomSupplierFinancingReading = prospectusReading
  "Broadcom-linked financing"
  "up to USD 42 billion associated with a five-year USD 125.2 billion compute-capacity commitment"
  reutersBroadcomLoan2026 false false

record SupplierFinancingLoopObservation : Set where
  constructor supplierFinancingLoopObservation
  field
    supplierOrAffiliateProvidesCapital : Bool
    customerUsesCapitalForSupplierLinkedCapacity : Bool
    supplierReceivesCommercialRevenue : Bool
    financingMayCreateEquityExposure : Bool
    provesCircularRevenue : Bool
    provesFraud : Bool

open SupplierFinancingLoopObservation public

anthropicBroadcomLoop : SupplierFinancingLoopObservation
anthropicBroadcomLoop =
  supplierFinancingLoopObservation true true true true false false

------------------------------------------------------------------------
-- Valuation / growth-duration boundary.
------------------------------------------------------------------------

record ValuationGrowthDuration : Set where
  constructor valuationGrowthDuration
  field
    valuationReading : String
    currentRevenueBasis : String
    futureRevenueBasis : String
    requiredGrowthReading : String
    forecastAchievementEstablished : Bool

open ValuationGrowthDuration public

candidateAnthropicGrowthDuration : ValuationGrowthDuration
candidateAnthropicGrowthDuration = valuationGrowthDuration
  "potential valuation above USD 2 trillion"
  "2025 booked revenue is far below the valuation scale"
  "reported 2028 revenue projection roughly USD 190-200 billion"
  "valuation therefore depends materially on several years of extreme growth and margin improvement"
  false

data ForecastRevenueImpliesCapitalRecoveryPermission : Set where
data SupplierLoanImpliesIndependentTerminalDemandPermission : Set where
data GAAPNetLossImpliesCashBurnPermission : Set where

forecastRevenueDoesNotAutoProveCapitalRecovery :
  ForecastRevenueImpliesCapitalRecoveryPermission → ⊥
forecastRevenueDoesNotAutoProveCapitalRecovery ()

supplierLoanDoesNotAutoProveIndependentTerminalDemand :
  SupplierLoanImpliesIndependentTerminalDemandPermission → ⊥
supplierLoanDoesNotAutoProveIndependentTerminalDemand ()

gaapNetLossDoesNotAutoEqualCashBurn :
  GAAPNetLossImpliesCashBurnPermission → ⊥
gaapNetLossDoesNotAutoEqualCashBurn ()

capitalSpreadType : Set₁
capitalSpreadType = Capital.AICapitalCrackSpread

surroundingSignalsStillNeedTerminalValidation :
  Terminal.SurroundingSignalsImplyEconomicValidationPermission → ⊥
surroundingSignalsStillNeedTerminalValidation =
  Terminal.surroundingSignalsDoNotAutoPromoteToEconomicValidation
