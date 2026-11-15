module DASHI.Economics.AICoreWeaveGenerationPriceLadder20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

companyPlatformKind : Source.SourceKind
companyPlatformKind = Source.namedSourceKind "primary company commercial pricing surface"

coreWeavePricingSource : Source.AttributedSource
coreWeavePricingSource = Source.mkNoDOISource
  "CoreWeave"
  "CoreWeave Cloud Pricing"
  "current North America on-demand GPU instance pricing"
  "2026-10"
  "https://www.coreweave.com/pricing"
  companyPlatformKind
  "primary carrier for selected current instance prices and GPU counts used to derive per-GPU-hour price coordinates: A100 8 GPUs USD21.60/h, H100 8 GPUs USD49.24/h, H200 8 GPUs USD50.44/h, B200 8 GPUs USD68.80/h, GB200 4 GPUs USD42.00/h"
  Source.publicAttribution

record GenerationPriceLadder : Set where
  constructor generation-price-ladder
  field
    provider : String
    a100PerGPUHourMills : Nat
    h100PerGPUHourMills : Nat
    h200PerGPUHourMills : Nat
    b200PerGPUHourMills : Nat
    gb200PerGPUHourMills : Nat
    sameDateCommercialCrossSection : Bool
    resourceBundlesIdentical : Bool
    realisedUtilisationObserved : Bool
    realisedASPObserved : Bool
    resaleResidualValueObserved : Bool
    longitudinalDepreciationCurveObserved : Bool
    positiveUnitEconomicsEstablished : Bool

open GenerationPriceLadder public

coreWeaveCurrentGenerationPriceLadder : GenerationPriceLadder
coreWeaveCurrentGenerationPriceLadder = generation-price-ladder
  "CoreWeave"
  2700 6155 6305 8600 10500
  true false false false false false false

a100PerGPUHourMillsIs2700 :
  a100PerGPUHourMills coreWeaveCurrentGenerationPriceLadder ≡ 2700
a100PerGPUHourMillsIs2700 = refl

h100PerGPUHourMillsIs6155 :
  h100PerGPUHourMills coreWeaveCurrentGenerationPriceLadder ≡ 6155
h100PerGPUHourMillsIs6155 = refl

h200PerGPUHourMillsIs6305 :
  h200PerGPUHourMills coreWeaveCurrentGenerationPriceLadder ≡ 6305
h200PerGPUHourMillsIs6305 = refl

b200PerGPUHourMillsIs8600 :
  b200PerGPUHourMills coreWeaveCurrentGenerationPriceLadder ≡ 8600
b200PerGPUHourMillsIs8600 = refl

gb200PerGPUHourMillsIs10500 :
  gb200PerGPUHourMills coreWeaveCurrentGenerationPriceLadder ≡ 10500
gb200PerGPUHourMillsIs10500 = refl

data PriceCrossSectionImpliesDepreciationCurvePermission : Set where
data ListedPriceImpliesRealisedASPPermission : Set where
data ListedPriceImpliesPositiveUnitEconomicsPermission : Set where

data CrossBundlePriceImpliesQualityAdjustedRentPermission : Set where

priceCrossSectionDoesNotIdentifyDepreciationCurve :
  PriceCrossSectionImpliesDepreciationCurvePermission → ⊥
priceCrossSectionDoesNotIdentifyDepreciationCurve ()

listedPriceDoesNotCreateRealisedASP : ListedPriceImpliesRealisedASPPermission → ⊥
listedPriceDoesNotCreateRealisedASP ()

listedPriceDoesNotProvePositiveUnitEconomics :
  ListedPriceImpliesPositiveUnitEconomicsPermission → ⊥
listedPriceDoesNotProvePositiveUnitEconomics ()

crossBundlePriceDoesNotCreateQualityAdjustedRent :
  CrossBundlePriceImpliesQualityAdjustedRentPermission → ⊥
crossBundlePriceDoesNotCreateQualityAdjustedRent ()

boundary : String
boundary =
  "CoreWeave's current North America on-demand catalog supports a same-date selected per-GPU-hour price cross-section: A100 USD2.70, H100 USD6.155, H200 USD6.305, B200 USD8.60 and GB200 USD10.50. This is useful evidence that older generations retain commercial price capacity while newer generations command different listed rents. The bundles differ in memory/CPU/storage/interconnect characteristics and listed prices are not realised utilisation or ASP, so the cross-section does not identify a longitudinal depreciation curve, resale residual value, quality-adjusted scarcity rent or positive unit economics."
