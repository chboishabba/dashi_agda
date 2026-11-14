module DASHI.Economics.AIMI355XAcquisitionDepreciationEnvelope20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

commercialListingKind : Source.SourceKind
commercialListingKind = Source.namedSourceKind "current commercial reseller listing"

lowQuoteSource : Source.AttributedSource
lowQuoteSource = Source.mkNoDOISource
  "RackMountNTS"
  "Gigabyte G4L3-ZX1-LAT4"
  "commercial reseller listing"
  "2026-10"
  "https://www.rackmountnts.com/gigabyte-g4l3-zx1-lat4"
  commercialListingKind
  "lists a starting price of USD 230,359 for a liquid-cooled server with eight AMD Instinct MI355X OAM GPUs; final BOM is quote/configuration dependent"
  Source.publicAttribution

highQuoteSource : Source.AttributedSource
highQuoteSource = Source.mkNoDOISource
  "AVA Direct"
  "Gigabyte G893-ZX1-AAX4 configured 8x MI355X system"
  "commercial reseller configurator"
  "2026-10"
  "https://avadirect.azureedge.net/GIGABYTE-G893-ZX1-AAX4-Dual-AMD-EPYC-9005-9004-Processors-8x-AMD-Instinct-MI355X-OAM-GPUs-8U-HPC-AI-Server/Configure/20113870"
  commercialListingKind
  "shows configured price USD 323,779 for an eight-MI355X server with two EPYC 9454 CPUs, 512GB RAM, 960GB NVMe and integrated networking; this configuration is not resource-identical to the selected Vultr rental node"
  Source.publicAttribution

record AcquisitionDepreciationEnvelope : Set where
  constructor acquisition-depreciation-envelope
  field
    lowEightGpuNodeQuoteUSD : Nat
    highEightGpuNodeQuoteUSD : Nat
    lowPerGPUThousandthUSD : Nat
    highPerGPUThousandthUSD : Nat
    fiveYearLowDepreciationPerGPUThousandthUSD : Nat
    fiveYearHighDepreciationPerGPUThousandthUSD : Nat
    sixYearLowDepreciationFloorPerGPUThousandthUSD : Nat
    sixYearHighDepreciationFloorPerGPUThousandthUSD : Nat
    annualRentalBudgetPerGPUThousandthUSD : Nat
    benchmarkElectricityPerGPUYearThousandthUSD : Nat
    fiveYearLowQuoteResidualHeadroomThousandthUSD : Nat
    fiveYearHighQuoteResidualHeadroomThousandthUSD : Nat
    purchaseQuoteRangeObserved : Bool
    matchedRentalNodePurchasePricePaid : Bool
    financingRatePaid : Bool
    facilityPUEPaid : Bool
    operationsPaid : Bool
    fullOwnedTCOPaid : Bool

open AcquisitionDepreciationEnvelope public

mi355xAcquisitionDepreciationEnvelope : AcquisitionDepreciationEnvelope
mi355xAcquisitionDepreciationEnvelope = acquisition-depreciation-envelope
  230359 323779
  28794875 40472375
  5758975 8094475
  4799145 6745395
  22688400 1405761
  15523664 13188164
  true false false false false false

lowEightGpuNodeQuoteUSDIs230359 :
  lowEightGpuNodeQuoteUSD mi355xAcquisitionDepreciationEnvelope ≡ 230359
lowEightGpuNodeQuoteUSDIs230359 = refl

highEightGpuNodeQuoteUSDIs323779 :
  highEightGpuNodeQuoteUSD mi355xAcquisitionDepreciationEnvelope ≡ 323779
highEightGpuNodeQuoteUSDIs323779 = refl

-- Exact quote allocation at eight GPUs, represented in thousandths of USD.
lowQuotePerGPUReconciliation : 28794875 * 8 ≡ 230359 * 1000
lowQuotePerGPUReconciliation = refl

highQuotePerGPUReconciliation : 40472375 * 8 ≡ 323779 * 1000
highQuotePerGPUReconciliation = refl

fiveYearLowQuoteDepreciationPerGPUThousandthUSDIs5758975 :
  fiveYearLowDepreciationPerGPUThousandthUSD mi355xAcquisitionDepreciationEnvelope ≡ 5758975
fiveYearLowQuoteDepreciationPerGPUThousandthUSDIs5758975 = refl

fiveYearHighQuoteDepreciationPerGPUThousandthUSDIs8094475 :
  fiveYearHighDepreciationPerGPUThousandthUSD mi355xAcquisitionDepreciationEnvelope ≡ 8094475
fiveYearHighQuoteDepreciationPerGPUThousandthUSDIs8094475 = refl

fiveYearLowQuoteDepreciationReconciliation : 5758975 * 5 ≡ 28794875
fiveYearLowQuoteDepreciationReconciliation = refl

fiveYearHighQuoteDepreciationReconciliation : 8094475 * 5 ≡ 40472375
fiveYearHighQuoteDepreciationReconciliation = refl

-- Six-year floors leave a five-thousandth-dollar remainder per GPU-year.
sixYearLowQuoteFloorReconciliation : 4799145 * 6 + 5 ≡ 28794875
sixYearLowQuoteFloorReconciliation = refl

sixYearHighQuoteFloorReconciliation : 6745395 * 6 + 5 ≡ 40472375
sixYearHighQuoteFloorReconciliation = refl

-- At five-year straight-line depreciation with zero residual value and the
-- existing benchmark electricity coordinate, the selected $2.59/GPU-hour
-- rental comparator leaves the following annual headroom for ALL remaining
-- owner costs: financing/opportunity cost, facility PUE, labour, unmatched
-- host/network/storage, maintenance, residual/refresh risk, etc.
fiveYearLowHeadroomReconciliation :
  5758975 + 1405761 + 15523664 ≡ 22688400
fiveYearLowHeadroomReconciliation = refl

fiveYearHighHeadroomReconciliation :
  8094475 + 1405761 + 13188164 ≡ 22688400
fiveYearHighHeadroomReconciliation = refl

purchaseQuoteRangePaid :
  purchaseQuoteRangeObserved mi355xAcquisitionDepreciationEnvelope ≡ true
purchaseQuoteRangePaid = refl

matchedRentalNodePurchasePriceStillOpen :
  matchedRentalNodePurchasePricePaid mi355xAcquisitionDepreciationEnvelope ≡ false
matchedRentalNodePurchasePriceStillOpen = refl

data PurchaseQuoteCreatesFullOwnedTCOPermission : Set where
data QuoteCreatesFinancingRatePermission : Set where
data ResellerQuoteCreatesCompletedTransactionPermission : Set where

purchaseQuoteDoesNotCreateFullOwnedTCO : PurchaseQuoteCreatesFullOwnedTCOPermission → ⊥
purchaseQuoteDoesNotCreateFullOwnedTCO ()

quoteDoesNotCreateFinancingRate : QuoteCreatesFinancingRatePermission → ⊥
quoteDoesNotCreateFinancingRate ()

resellerQuoteDoesNotCreateCompletedTransaction : ResellerQuoteCreatesCompletedTransactionPermission → ⊥
resellerQuoteDoesNotCreateCompletedTransaction ()

boundary : String
boundary =
  "Current reseller listings pay a bounded 8xMI355X acquisition-price surface: USD 230,359 starting and USD 323,779 for one configured system. Dividing those quote values across eight GPUs gives exact quote-basis acquisition coordinates and therefore explicit five-year straight-line depreciation of about USD 5,758.975 to USD 8,094.475 per GPU-year before residual value. Combined with the existing USD 22,688.40 annual rental budget and USD 1,405.761 benchmark hardware-electricity coordinate, this leaves about USD 15,523.664 to USD 13,188.164 per GPU-year for financing, PUE, labour, unmatched host/network/storage, maintenance, residual and refresh costs before selected-rental parity. The listings are commercial quotes, not completed transactions; their node resources do not exactly match the selected rental node, and no financing rate is inferred."
