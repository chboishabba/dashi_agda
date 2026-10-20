module DASHI.Economics.AIEnergyCapitalBottleneck20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

internationalAgencyReportKind : Source.SourceKind
internationalAgencyReportKind = Source.namedSourceKind "international-agency technical policy report"

ieaPoweringAISource : Source.AttributedSource
ieaPoweringAISource = Source.mkNoDOISource
  "International Energy Agency"
  "Powering Artificial Intelligence"
  "G7-requested technical policy report"
  "2026-10-14"
  "https://www.iea.org/reports/powering-artificial-intelligence"
  internationalAgencyReportKind
  "reports hyperscalers set to spend more than USD700B capex in 2026, grid/supply-chain constraints, uncertainty over data-centre load ramp and AI profitability, and policy responses around connection queues"
  Source.publicAttribution

ieaKeyQuestionsSource : Source.AttributedSource
ieaKeyQuestionsSource = Source.mkNoDOISource
  "International Energy Agency"
  "Key Questions on Energy and AI"
  "energy-and-AI assessment"
  "2026"
  "https://www.iea.org/reports/key-questions-on-energy-and-ai/executive-summary"
  internationalAgencyReportKind
  "projects data-centre electricity use roughly doubling from 485 TWh in 2025 to 950 TWh in 2030, with AI-focused data-centre use tripling; states buildout now requires large capital-market funding and is sensitive to market sentiment and expected returns"
  Source.publicAttribution

record EnergyCapitalBottleneck : Set where
  constructor energy-capital-bottleneck
  field
    hyperscalerCapexBillionUSDLowerBound : Nat
    dataCentreElectricity2025TWh : Nat
    dataCentreElectricity2030TWh : Nat
    capitalMarketFundingRequired : Bool
    gridAndSupplyChainBottlenecksPaid : Bool
    demandRampUncertain : Bool
    profitabilityUncertain : Bool
    physicalBuildoutPaid : Bool
    financialReturnPaid : Bool
    universalCapacityShortagePaid : Bool

open EnergyCapitalBottleneck public

currentEnergyCapitalBottleneck : EnergyCapitalBottleneck
currentEnergyCapitalBottleneck = energy-capital-bottleneck
  700 485 950 true true true true true false false

hyperscalerCapexFloorPaid :
  hyperscalerCapexBillionUSDLowerBound currentEnergyCapitalBottleneck ≡ 700
hyperscalerCapexFloorPaid = refl

data PhysicalBuildoutImpliesReturnPermission : Set where
data QueuePressureImpliesUniversalShortagePermission : Set where

physicalBuildoutDoesNotCreateFinancialReturn : PhysicalBuildoutImpliesReturnPermission → ⊥
physicalBuildoutDoesNotCreateFinancialReturn ()

queuePressureDoesNotCreateUniversalCapacityShortage : QueuePressureImpliesUniversalShortagePermission → ⊥
queuePressureDoesNotCreateUniversalCapacityShortage ()

boundary : String
boundary =
  "IEA October-2026 evidence strengthens the physical side of the AI-capital thesis rather than resolving the financial side. Hyperscaler 2026 capex exceeds USD700B and the central data-centre electricity projection rises from 485 TWh in 2025 to 950 TWh in 2030; grid, equipment, chip and capital constraints are real. The same reports explicitly retain uncertainty about load ramp, profitability and financing conditions. Physical infrastructure demand therefore cannot be collapsed into investor return, and queue pressure is not a universal shortage theorem."
