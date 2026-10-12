module DASHI.Economics.AISameModelSelfHostCostBoundary20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- SAME-MODEL HOSTED-vs-RENTED-GPU SERVING COST BOUNDARY
--
-- The public source computes cost from an on-demand GPU rental tariff:
--
--   (GPU hourly rental rate * GPU count)
--   / (output throughput * 3600 * utilisation) * 1,000,000.
--
-- It therefore pays a rented-capacity serving-cost comparison.  Any energy,
-- asset depreciation and capital cost borne by the GPU lessor may be reflected
-- economically in the rental tariff, but those components are not separately
-- identified or auditable in the source.  It is NOT an owned-hardware TCO
-- model: engineer time is explicitly excluded and owner-side depreciation,
-- electricity/PUE, financing/opportunity cost, residual value, non-GPU host /
-- network/storage cost, maintenance and refresh risk are not decomposed.
------------------------------------------------------------------------

engineeringDatasetKind : Source.SourceKind
engineeringDatasetKind = Source.namedSourceKind "public engineering cost dataset with disclosed vendor conflict"

inferenceCostTruthSource : Source.AttributedSource
inferenceCostTruthSource = Source.mkNoDOISource
  "RightNow AI"
  "inference-cost-truth"
  "GitHub engineering dataset / 2026-07-31 snapshot"
  "2026-07-31"
  "https://github.com/RightNow-AI/inference-cost-truth/tree/a61c501241da17f3403597d75a7a8847c53cb29e"
  engineeringDatasetKind
  "source computes same-model serving cost from published on-demand GPU rental rate, GPU count, measured output throughput and assumed utilisation; MiniMax-M3 on AMD MI355X at concurrency 512 and 30 percent sustained utilisation is estimated at USD 0.93 per million output tokens versus USD 1.20 hosted; engineer time is explicitly excluded"
  Source.publicAttribution

record SameModelCostComparison : Set where
  constructor same-model-cost-comparison
  field
    model : String
    hostedProviderClass : String
    accelerator : String
    concurrency : Nat
    inputTokens : Nat
    utilizationPercent : Nat
    selfHostCostCentsPerMillionOutput : Nat
    hostedCostCentsPerMillionOutput : Nat
    sameModelIdentity : Bool
    configurationSensitive : Bool
    sourceConflictDisclosed : Bool
    gpuRentalTariffBasis : Bool
    ownedHardwareTCO : Bool
    separateDepreciationModelPaid : Bool
    separateEnergyModelPaid : Bool
    separateFinancingCostPaid : Bool
    separateNonGPUInfrastructurePaid : Bool
    separateResidualValuePaid : Bool
    engineerTimePaid : Bool
    directProviderMarginalCostObserved : Bool
    frontierClosedModelComparator : Bool
    globalSelfHostAdvantageEstablished : Bool
    source : Source.AttributedSource

open SameModelCostComparison public

miniMaxM3EngineeringComparison : SameModelCostComparison
miniMaxM3EngineeringComparison = same-model-cost-comparison
  "MiniMax-M3"
  "hosted open-model API"
  "AMD MI355X"
  512
  1000
  30
  93
  120
  true
  true
  true
  true
  false
  false
  false
  false
  false
  false
  false
  false
  false
  false
  inferenceCostTruthSource

sameModelIdentityPaid : sameModelIdentity miniMaxM3EngineeringComparison ≡ true
sameModelIdentityPaid = refl

selfHostCostCentsPerMillionIs93 :
  selfHostCostCentsPerMillionOutput miniMaxM3EngineeringComparison ≡ 93
selfHostCostCentsPerMillionIs93 = refl

hostedCostCentsPerMillionIs120 :
  hostedCostCentsPerMillionOutput miniMaxM3EngineeringComparison ≡ 120
hostedCostCentsPerMillionIs120 = refl

configurationSensitivityRetained :
  configurationSensitive miniMaxM3EngineeringComparison ≡ true
configurationSensitivityRetained = refl

gpuRentalTariffBasisPaid :
  gpuRentalTariffBasis miniMaxM3EngineeringComparison ≡ true
gpuRentalTariffBasisPaid = refl

ownedHardwareTCOPaidIsFalse :
  ownedHardwareTCO miniMaxM3EngineeringComparison ≡ false
ownedHardwareTCOPaidIsFalse = refl

separateDepreciationModelPaidIsFalse :
  separateDepreciationModelPaid miniMaxM3EngineeringComparison ≡ false
separateDepreciationModelPaidIsFalse = refl

separateEnergyModelPaidIsFalse :
  separateEnergyModelPaid miniMaxM3EngineeringComparison ≡ false
separateEnergyModelPaidIsFalse = refl

separateFinancingCostPaidIsFalse :
  separateFinancingCostPaid miniMaxM3EngineeringComparison ≡ false
separateFinancingCostPaidIsFalse = refl

engineerTimePaidIsFalse :
  engineerTimePaid miniMaxM3EngineeringComparison ≡ false
engineerTimePaidIsFalse = refl

providerMarginalCostStillUnobserved :
  directProviderMarginalCostObserved miniMaxM3EngineeringComparison ≡ false
providerMarginalCostStillUnobserved = refl

data EngineeringCostImpliesProviderMarginPermission : Set where
data OneFavourableConfigurationImpliesGlobalSelfHostAdvantagePermission : Set where
data HostedOpenComparatorImpliesClosedModelScarcityRentPermission : Set where
data RentalTariffImpliesOwnedHardwareTCOPermission : Set where

engineeringCostDoesNotCreateProviderMargin :
  EngineeringCostImpliesProviderMarginPermission → ⊥
engineeringCostDoesNotCreateProviderMargin ()

oneConfigurationDoesNotCreateGlobalSelfHostAdvantage :
  OneFavourableConfigurationImpliesGlobalSelfHostAdvantagePermission → ⊥
oneConfigurationDoesNotCreateGlobalSelfHostAdvantage ()

hostedOpenDoesNotCreateClosedModelScarcityRent :
  HostedOpenComparatorImpliesClosedModelScarcityRentPermission → ⊥
hostedOpenDoesNotCreateClosedModelScarcityRent ()

rentalTariffDoesNotCreateOwnedHardwareTCO :
  RentalTariffImpliesOwnedHardwareTCOPermission → ⊥
rentalTariffDoesNotCreateOwnedHardwareTCO ()

record ServingCostResidual : Set where
  constructor serving-cost-residual
  field
    sameModelRentedGPUComparatorPaid : Bool
    ownedHardwareTCOModelPaid : Bool
    providerOwnMarginalCostLedgerPaid : Bool
    matchedLatencySLAPaid : Bool
    matchedCachingPolicyPaid : Bool
    matchedUtilizationPaid : Bool
    qualityAdjustedClosedOpenMarginPaid : Bool

open ServingCostResidual public

currentServingCostResidual : ServingCostResidual
currentServingCostResidual = serving-cost-residual
  true false false false false false false

boundary : String
boundary =
  "The 2026-07-31 inference-cost-truth snapshot supplies a same-model MiniMax-M3 RENTED-GPU comparison: under MI355X, concurrency 512, 1k input and 30 percent sustained utilisation, a published on-demand GPU tariff plus measured throughput gives USD 0.93/M output tokens versus USD 1.20/M hosted. The rental price may economically bundle costs borne by the lessor, but the source does not separately identify depreciation, energy/PUE, financing/opportunity cost, non-GPU infrastructure, residual value or refresh risk and explicitly excludes engineer time. Therefore this is not an owned-hardware TCO receipt, does not reveal the hosted provider's own marginal cost, does not establish global self-host advantage, and does not create a closed-vs-open scarcity-rent theorem."
