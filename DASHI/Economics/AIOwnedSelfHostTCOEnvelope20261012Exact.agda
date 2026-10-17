module DASHI.Economics.AIOwnedSelfHostTCOEnvelope20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- OWNED SELF-HOST TCO ENVELOPE
--
-- This owner does NOT guess a GPU/server purchase price.  Instead it asks:
-- given the source-paid $2.59/GPU-hour rental comparator, what all-in owned
-- hourly/annual cost must an owner beat?  We then pay only one independently
-- observed TCO component: reference-system electricity at a public benchmark
-- industrial electricity price.
--
-- The selected rental tariff is also not a bare-GPU silicon price: Vultr's
-- published eight-GPU MI355X configuration includes host CPU/RAM/storage and
-- bandwidth.  Therefore an ownership comparison must be a matched node/service
-- envelope, not simply GPU purchase price versus cloud GPU-hour price.
------------------------------------------------------------------------

primaryVendorKind : Source.SourceKind
primaryVendorKind = Source.namedSourceKind "primary vendor reference design"

officialEnergyKind : Source.SourceKind
officialEnergyKind = Source.namedSourceKind "official electricity price statistics"

engineeringDatasetKind : Source.SourceKind
engineeringDatasetKind = Source.namedSourceKind "public engineering cost dataset"

primaryProviderPricingKind : Source.SourceKind
primaryProviderPricingKind = Source.namedSourceKind "primary cloud-provider pricing page"

amdReferenceDesignSource : Source.AttributedSource
amdReferenceDesignSource = Source.mkNoDOISource
  "AMD"
  "AMD Instinct MI3XX Reference Design - MI355X power requirements"
  "vendor reference design"
  "2026"
  "https://instinct.docs.amd.com/projects/MI3XX-reference/latest/index.html"
  primaryVendorKind
  "reference design assumes approximately 14kW average power per eight-GPU MI355X system, or 1.75kW per GPU-equivalent before separate facility-PUE allocation"
  Source.publicAttribution

eiaJune2026Source : Source.AttributedSource
eiaJune2026Source = Source.mkNoDOISource
  "U.S. Energy Information Administration"
  "Electric Power Monthly Table 5.3"
  "official electricity statistics"
  "2026-08-26"
  "https://www.eia.gov/electricity/monthly/epm_table_grapher.php?t=epmt_5_03"
  officialEnergyKind
  "June 2026 US industrial average electricity price is 9.17 cents per kWh"
  Source.publicAttribution

rentalComparatorSource : Source.AttributedSource
rentalComparatorSource = Source.mkNoDOISource
  "RightNow AI"
  "inference-cost-truth"
  "GitHub engineering dataset / 2026-07-31 snapshot"
  "2026-07-31"
  "https://github.com/RightNow-AI/inference-cost-truth/tree/a61c501241da17f3403597d75a7a8847c53cb29e"
  engineeringDatasetKind
  "selected MI355X comparison uses USD 2.59 per GPU-hour rental price and explicitly excludes engineer time"
  Source.publicAttribution

vultrNodePricingSource : Source.AttributedSource
vultrNodePricingSource = Source.mkNoDOISource
  "Vultr"
  "AMD MI355X Cloud GPU / Bare Metal pricing"
  "provider pricing page"
  "2026-10-14"
  "https://www.vultr.com/pricing/"
  primaryProviderPricingKind
  "published MI355X configuration: eight GPUs, 2304GB aggregate GPU RAM, 252 vCPUs, 2872GB RAM, 14.34TB storage, 15TB bandwidth, price starting at USD 2.590 per GPU-hour"
  Source.publicAttribution

record OwnedTCOEnvelope : Set where
  constructor owned-tco-envelope
  field
    accelerator : String
    referenceSystemWattsPerGPU : Nat
    industrialElectricityHundredthCentPerKWh : Nat
    rentalTariffCentsPerGPUHour : Nat
    rentalNodeGPUCount : Nat
    rentalNodeVCPUCount : Nat
    rentalNodeRAMGiB : Nat
    rentalNodeStorageHundredthTB : Nat
    rentalNodeBandwidthTB : Nat
    rentalNodeIncludesHostResources : Bool
    benchmarkElectricityHundredthCentPerGPUHour : Nat
    annualRentalBudgetCentsPerGPU : Nat
    annualNonElectricHeadroomCentsPerGPU : Nat
    purchasePricePaid : Bool
    ownerFinancingCostPaid : Bool
    facilityPUEPaid : Bool
    operationsLabourPaid : Bool
    matchedOwnerHostInfrastructurePaid : Bool
    residualValuePaid : Bool
    refreshFailureRiskPaid : Bool
    ownedTCOPaid : Bool

open OwnedTCOEnvelope public

mi355xOwnedEnvelope : OwnedTCOEnvelope
mi355xOwnedEnvelope = owned-tco-envelope
  "AMD MI355X"
  1750
  917
  259
  8
  252
  2872
  1434
  15
  true
  1605
  2268840
  2128264
  false false false false false false false false

mi355xReferenceSystemWattsPerGPUIs1750 :
  referenceSystemWattsPerGPU mi355xOwnedEnvelope ≡ 1750
mi355xReferenceSystemWattsPerGPUIs1750 = refl

usIndustrialElectricityJune2026Is917HundredthCentPerKWh :
  industrialElectricityHundredthCentPerKWh mi355xOwnedEnvelope ≡ 917
usIndustrialElectricityJune2026Is917HundredthCentPerKWh = refl

rentalTariffCentsPerGPUHourIs259 :
  rentalTariffCentsPerGPUHour mi355xOwnedEnvelope ≡ 259
rentalTariffCentsPerGPUHourIs259 = refl

rentalNodeGPUCountIs8 : rentalNodeGPUCount mi355xOwnedEnvelope ≡ 8
rentalNodeGPUCountIs8 = refl

rentalNodeVCPUCountIs252 : rentalNodeVCPUCount mi355xOwnedEnvelope ≡ 252
rentalNodeVCPUCountIs252 = refl

rentalNodeRAMGiBIs2872 : rentalNodeRAMGiB mi355xOwnedEnvelope ≡ 2872
rentalNodeRAMGiBIs2872 = refl

rentalNodeIncludesHostResourcesPaid : rentalNodeIncludesHostResources mi355xOwnedEnvelope ≡ true
rentalNodeIncludesHostResourcesPaid = refl

-- Exact raw multiplication behind 1.75kW * 9.17 cents/kWh:
benchmarkElectricityRawProduct : 1750 * 917 ≡ 1604750
benchmarkElectricityRawProduct = refl

benchmarkElectricityCostAbout1605HundredthCentPerGPUHour :
  benchmarkElectricityHundredthCentPerGPUHour mi355xOwnedEnvelope ≡ 1605
benchmarkElectricityCostAbout1605HundredthCentPerGPUHour = refl

annualRentalBudgetPerGPUIs2268840Cents :
  annualRentalBudgetCentsPerGPU mi355xOwnedEnvelope ≡ 2268840
annualRentalBudgetPerGPUIs2268840Cents = refl

annualNonElectricHeadroomAbout2128264Cents :
  annualNonElectricHeadroomCentsPerGPU mi355xOwnedEnvelope ≡ 2128264
annualNonElectricHeadroomAbout2128264Cents = refl

purchasePriceStillOpen : purchasePricePaid mi355xOwnedEnvelope ≡ false
purchasePriceStillOpen = refl

ownedTCOStillOpen : ownedTCOPaid mi355xOwnedEnvelope ≡ false
ownedTCOStillOpen = refl

data ElectricityBenchmarkImpliesFullTCOPermission : Set where
data RentalBreakEvenImpliesOwnershipAdvantagePermission : Set where
data BundledRentalNodeImpliesMatchedOwnedNodePermission : Set where

electricityBenchmarkDoesNotCreateFullTCO : ElectricityBenchmarkImpliesFullTCOPermission → ⊥
electricityBenchmarkDoesNotCreateFullTCO ()

rentalBreakEvenDoesNotCreateOwnershipAdvantage : RentalBreakEvenImpliesOwnershipAdvantagePermission → ⊥
rentalBreakEvenDoesNotCreateOwnershipAdvantage ()

bundledRentalDoesNotCreateMatchedOwnerNode : BundledRentalNodeImpliesMatchedOwnedNodePermission → ⊥
bundledRentalDoesNotCreateMatchedOwnerNode ()

boundary : String
boundary =
  "For the selected MI355X comparison, USD 2.59/GPU-hour implies an annual rental budget of USD 22,688.40 per continuously provisioned GPU. The current Vultr listing shows that this tariff belongs to an eight-GPU node that also includes 252 vCPUs, 2872GB RAM, 14.34TB storage and 15TB bandwidth: it is a bundled service/node tariff rather than bare-silicon cost. AMD's reference design implies about 1.75kW average system power per GPU-equivalent; at the EIA June-2026 US industrial average 9.17c/kWh, benchmark hardware electricity is about USD 1,405.76/GPU-year, leaving about USD 21,282.64/GPU-year for every other matched ownership cost before reaching the rental tariff. Purchase price/depreciation, financing/opportunity cost, facility PUE, labour, matched owner-side host/network/storage, residual value and refresh risk remain unpaid, so owned-hardware TCO and ownership advantage remain open."
