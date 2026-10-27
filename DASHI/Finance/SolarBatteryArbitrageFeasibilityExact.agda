module DASHI.Finance.SolarBatteryArbitrageFeasibilityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; _<_)

import DASHI.Cognition.CausalRegimeMeasureFrame as Frames
import DASHI.Finance.DeepStatArbFibrePipelineExact as StatArb

------------------------------------------------------------------------
-- SOLAR / BATTERY / GRID ARBITRAGE FEASIBILITY
--
-- Source authority stays with each named retailer or market operator.
-- Retrieval date for the source receipts below: 2026-10-27.
-- Repository formalisation does not turn a tariff snapshot into a future
-- tariff promise, an eligibility decision, an installation approval, or a
-- guaranteed investment return.
--
-- Reused repository owners:
-- * DASHI.Cognition.CausalRegimeMeasureFrame
-- * DASHI.Finance.DeepStatArbFibrePipelineExact
--
-- No ESD surface is modified or re-owned here.
-- meta-introspector repository attribution remains external and unchanged.
------------------------------------------------------------------------

data ValueChannel : Set where
  avoidedImport : ValueChannel
  exportRevenue : ValueChannel

avoidedImport≠exportRevenue : avoidedImport ≡ exportRevenue → ⊥
avoidedImport≠exportRevenue ()

data ThroughputLimiter : Set where
  batteryCapacity : ThroughputLimiter
  chargePower : ThroughputLimiter
  dischargePower : ThroughputLimiter
  chargeWindow : ThroughputLimiter
  dischargeWindow : ThroughputLimiter
  retailerChargeCap : ThroughputLimiter
  retailerExportCap : ThroughputLimiter
  householdDeferredLoad : ThroughputLimiter
  connectionLimit : ThroughputLimiter
  tariffTerms : ThroughputLimiter

canonicalThroughputLimiters : List ThroughputLimiter
canonicalThroughputLimiters =
  batteryCapacity
  ∷ chargePower
  ∷ dischargePower
  ∷ chargeWindow
  ∷ dischargeWindow
  ∷ retailerChargeCap
  ∷ retailerExportCap
  ∷ householdDeferredLoad
  ∷ connectionLimit
  ∷ tariffTerms
  ∷ []

record TariffSourceReceipt : Set where
  constructor tariffSourceReceipt
  field
    provider : String
    plan : String
    sourceURL : String
    accessedDate : String
    establishedTerms : String
    sourceBoundary : String

open TariffSourceReceipt public

originBatteryChargeSource : TariffSourceReceipt
originBatteryChargeSource =
  tariffSourceReceipt
    "Origin Energy"
    "Origin Battery Charge"
    "https://www.originenergy.com.au/solar/battery-plans/origin-battery-charge/"
    "2026-10-27"
    "Up to 28 kWh free grid electricity from 11am-3pm; 11 c/kWh peak export credit from 6pm-9pm for up to 10 kWh; smart meter required; embedded-network customers cannot take the offer."
    "The source describes the offer for solar-and-battery customers. This receipt does not assert battery-only eligibility for a specific apartment."

ovoFree4Source : TariffSourceReceipt
ovoFree4Source =
  tariffSourceReceipt
    "OVO Energy Australia"
    "Free 4"
    "https://pages.ovoenergy.com.au/the-free-4-plan"
    "2026-10-27"
    "Eligible usage is priced at 0.00 AUD/kWh from 11am-3pm every day; supply charges still apply; usage is subject to the Fair Use Policy."
    "This source receipt establishes a current retail window only. It does not establish future rates, battery compatibility, embedded-network eligibility, or site approval."

aglBatteryRewardsSource : TariffSourceReceipt
aglBatteryRewardsSource =
  tariffSourceReceipt
    "AGL"
    "Battery Rewards Plan"
    "https://www.agl.com.au/residential/solar-and-batteries"
    "2026-10-27"
    "AGL advertises 28 c/kWh feed-in credits for battery exports between 5pm-9pm and separately documents customer-controlled battery scheduling."
    "This receipt does not establish that every battery, site, tariff class, or apartment is eligible."

diamondWattbankSource : TariffSourceReceipt
diamondWattbankSource =
  tariffSourceReceipt
    "Diamond Energy"
    "WATTBANK VPP"
    "https://diamondenergy.com.au/diamond-energy-vpp/"
    "2026-10-27"
    "Diamond advertises 30 c/kWh Battery Usage Credit for grid exports between 6pm-8am plus an annual VPP credit subject to eligibility and continued VPP access/control."
    "This is a controlled VPP offer. The advertised export credit does not create customer-controlled dispatch authority or guaranteed annual revenue."

amberSmartShiftSource : TariffSourceReceipt
amberSmartShiftSource =
  tariffSourceReceipt
    "Amber Electric"
    "Amber for Batteries / SmartShift"
    "https://help.amber.com.au/hc/en-us/articles/10014159451405-How-does-SmartShift-work"
    "2026-10-27"
    "SmartShift forecasts household use, solar generation and wholesale prices to plan battery charging and export; compatibility constraints apply."
    "Wholesale-price opportunity is variable. A forecast, historical spike, or optimisation plan is not a guaranteed realised return."

currentTariffSourceAtlas : List TariffSourceReceipt
currentTariffSourceAtlas =
  originBatteryChargeSource
  ∷ ovoFree4Source
  ∷ aglBatteryRewardsSource
  ∷ diamondWattbankSource
  ∷ amberSmartShiftSource
  ∷ []

record StorageArbitrageInputs : Set where
  constructor storageArbitrageInputs
  field
    deliveredChargeCostMilliCentsPerKWh : ℕ
    dischargeValueMilliCentsPerKWh : ℕ
    usableCapacityWh : ℕ
    chargePowerW : ℕ
    dischargePowerW : ℕ
    chargeWindowMinutes : ℕ
    dischargeWindowMinutes : ℕ
    householdDeferredLoadWh : ℕ
    exportAllowanceWh : ℕ
    fixedCostCents : ℕ
    cycleCostMilliCentsPerKWh : ℕ
    tariffCurrent : Bool
    intervalMeteringAvailable : Bool
    connectionCompatible : Bool
    retailerEligibilityConfirmed : Bool

open StorageArbitrageInputs public

GrossUnitSpreadPositive : StorageArbitrageInputs → Set
GrossUnitSpreadPositive state =
  deliveredChargeCostMilliCentsPerKWh state
  < dischargeValueMilliCentsPerKWh state

record NetProfitReceipt (state : StorageArbitrageInputs) : Set where
  constructor netProfitReceipt
  field
    realisedRevenueCents : ℕ
    realisedVariableCostCents : ℕ
    realisedFixedCostCents : ℕ
    totalCostBelowRevenue :
      realisedVariableCostCents
      < realisedRevenueCents

open NetProfitReceipt public

record DispatchRoute : Set where
  constructor dispatchRoute
  field
    channel : ValueChannel
    dispatchedWh : ℕ

open DispatchRoute public

record TradingCapacityWitness : Set where
  constructor tradingCapacityWitness
  field
    householdRoute : DispatchRoute
    exportRoute : DispatchRoute
    householdRouteIsAvoidedImport : channel householdRoute ≡ avoidedImport
    exportRouteIsExportRevenue : channel exportRoute ≡ exportRevenue

open TradingCapacityWitness public

------------------------------------------------------------------------
-- Exact non-promotion boundaries.
------------------------------------------------------------------------

data GrossSpreadCreatesNetProfit : Set where

grossSpreadDoesNotCreateNetProfit :
  GrossSpreadCreatesNetProfit → ⊥
grossSpreadDoesNotCreateNetProfit ()

data LowHouseholdLoadCapsTradableThroughput : Set where

lowHouseholdLoadDoesNotCapTradableThroughput :
  LowHouseholdLoadCapsTradableThroughput → ⊥
lowHouseholdLoadDoesNotCapTradableThroughput ()

data TariffSnapshotCreatesFutureTariff : Set where

tariffSnapshotDoesNotCreateFutureTariff :
  TariffSnapshotCreatesFutureTariff → ⊥
tariffSnapshotDoesNotCreateFutureTariff ()

data SmartMeterCreatesSavings : Set where

smartMeterDoesNotCreateSavings :
  SmartMeterCreatesSavings → ⊥
smartMeterDoesNotCreateSavings ()

data SeparateEVNMICreatesApartmentTariffEligibility : Set where

separateEVNMIDoesNotCreateApartmentTariffEligibility :
  SeparateEVNMICreatesApartmentTariffEligibility → ⊥
separateEVNMIDoesNotCreateApartmentTariffEligibility ()

data CommonPropertySolarCreatesApartmentAccess : Set where

commonPropertySolarDoesNotCreateApartmentAccess :
  CommonPropertySolarCreatesApartmentAccess → ⊥
commonPropertySolarDoesNotCreateApartmentAccess ()

data ExistingConduitCreatesElectricalCompatibility : Set where

existingConduitDoesNotCreateElectricalCompatibility :
  ExistingConduitCreatesElectricalCompatibility → ⊥
existingConduitDoesNotCreateElectricalCompatibility ()

data RetailerIncentiveCreatesGuaranteedPayback : Set where

retailerIncentiveDoesNotCreateGuaranteedPayback :
  RetailerIncentiveCreatesGuaranteedPayback → ⊥
retailerIncentiveDoesNotCreateGuaranteedPayback ()

data SourceExampleCreatesUniversalOptimalBatterySize : Set where

sourceExampleDoesNotCreateUniversalOptimalBatterySize :
  SourceExampleCreatesUniversalOptimalBatterySize → ⊥
sourceExampleDoesNotCreateUniversalOptimalBatterySize ()

------------------------------------------------------------------------
-- Reused market-frame boundaries.
------------------------------------------------------------------------

batteryPricingFrame : Frames.EvaluationFrame
batteryPricingFrame = Frames.pricingFrame

batteryProbabilityRoleBoundary : Frames.ProbabilityRoleBoundary
batteryProbabilityRoleBoundary = Frames.canonicalProbabilityRoleBoundary

batteryStatArbBoundaryStatement : String
batteryStatArbBoundaryStatement = StatArb.pipelineBoundaryStatement

------------------------------------------------------------------------
-- ZKP O/R/C/S/L/P/G/F receipt.
------------------------------------------------------------------------

record BatteryArbitrageZKPFrame : Set where
  constructor batteryArbitrageZKPFrame
  field
    objective : String
    reuse : String
    construction : String
    safety : String
    lane : String
    preconditions : String
    invariants : String
    postconditions : String
    governance : String
    verification : String

open BatteryArbitrageZKPFrame public

canonicalBatteryArbitrageZKPFrame : BatteryArbitrageZKPFrame
canonicalBatteryArbitrageZKPFrame =
  batteryArbitrageZKPFrame
    "O: decide battery feasibility from exact tariff, physical, load, export, connection, and cost coordinates."
    "R: reuse the repository pricing/no-arbitrage frame and stat-arb fibre boundary; retain retailer source attribution."
    "C: separate avoided-import value from export-revenue value and keep every throughput limiter explicit."
    "S: no tariff snapshot, positive spread, smart meter, EV ownership, common solar, conduit path, or incentive promotes itself to eligibility, compatibility, net profit, or payback."
    "L: one canonical Finance owner; TOE files only import and re-export its proof surface."
    "P: use current source terms, interval load data, battery efficiency/capacity/power, connection limits, retailer eligibility, and full costs before a site conclusion."
    "P: household load and tradable export are distinct value channels; source evidence and repository theorem authority remain distinct."
    "P: TOE consumers can state exact non-promotion results without owning retailer facts or creating financial advice."
    "G: ITIL, ISO 9000/42001/27001/27701/23894/9241, NIST AI RMF, Six Sigma, and C4/PlantUML remain process lenses only."
    "F: zero postulates and zero unsafe compiler escapes; kernel and preflight receipts remain separate execution evidence."
