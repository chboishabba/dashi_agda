module DASHI.Economics.AICoreWeaveMultiGenerationCommercialCoexistence20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

companyPlatformKind : Source.SourceKind
companyPlatformKind = Source.namedSourceKind "primary company commercial platform"

coreWeavePricingSource : Source.AttributedSource
coreWeavePricingSource = Source.mkNoDOISource
  "CoreWeave"
  "CoreWeave Cloud Pricing"
  "current commercial platform"
  "2026-10"
  "https://www.coreweave.com/pricing"
  companyPlatformKind
  "primary commercial surface currently listing NVIDIA A100, H100, H200, GH200, B200/B300 and GB200/GB300 offerings; listing establishes commercial availability, not fleet share, utilisation or profitability"
  Source.publicAttribution

coreWeaveRubinProductionSource : Source.AttributedSource
coreWeaveRubinProductionSource = Source.mkNoDOISource
  "CoreWeave"
  "CoreWeave Delivers NVIDIA Vera Rubin NVL72 Performance at Production Scale, Starting With Cognition"
  "CoreWeave"
  "2026-09-30"
  "https://www.coreweave.com/news/coreweave-delivers-nvidia-vera-rubin-nvl72-performance-at-production-scale-starting-with-cognition"
  (Source.namedSourceKind "primary company publication")
  "primary carrier for Vera Rubin production customer workloads and deployment of hundreds of Rubin GPUs across multiple regions"
  Source.publicAttribution

record MultiGenerationCommercialCoexistence : Set where
  constructor multi-generation-commercial-coexistence
  field
    provider : String
    a100StillOffered : Bool
    h100StillOffered : Bool
    h200StillOffered : Bool
    gb200StillOffered : Bool
    b200StillOffered : Bool
    gb300StillOffered : Bool
    b300StillOffered : Bool
    rubinProductionPaid : Bool
    commercialListingDeterminesFleetShare : Bool
    commercialListingDeterminesUtilisation : Bool
    commercialListingDeterminesPositiveUnitEconomics : Bool
    successorArrivalDeterminesPriorGenerationExit : Bool

open MultiGenerationCommercialCoexistence public

coreWeaveCurrentCommercialCoexistence : MultiGenerationCommercialCoexistence
coreWeaveCurrentCommercialCoexistence = multi-generation-commercial-coexistence
  "CoreWeave"
  true true true true true true true true
  false false false false

a100StillOfferedReceipt : a100StillOffered coreWeaveCurrentCommercialCoexistence ≡ true
a100StillOfferedReceipt = refl

h100StillOfferedReceipt : h100StillOffered coreWeaveCurrentCommercialCoexistence ≡ true
h100StillOfferedReceipt = refl

h200StillOfferedReceipt : h200StillOffered coreWeaveCurrentCommercialCoexistence ≡ true
h200StillOfferedReceipt = refl

rubinProductionPaidReceipt : rubinProductionPaid coreWeaveCurrentCommercialCoexistence ≡ true
rubinProductionPaidReceipt = refl

data SuccessorImpliesPriorGenerationCommercialExitPermission : Set where
data ListingImpliesFleetSharePermission : Set where
data ListingImpliesPositiveUnitEconomicsPermission : Set where

successorDoesNotImplyPriorGenerationCommercialExit :
  SuccessorImpliesPriorGenerationCommercialExitPermission → ⊥
successorDoesNotImplyPriorGenerationCommercialExit ()

commercialListingDoesNotIdentifyFleetShare : ListingImpliesFleetSharePermission → ⊥
commercialListingDoesNotIdentifyFleetShare ()

commercialListingDoesNotProvePositiveUnitEconomics :
  ListingImpliesPositiveUnitEconomicsPermission → ⊥
commercialListingDoesNotProvePositiveUnitEconomics ()

boundary : String
boundary =
  "CoreWeave's current commercial pricing surface continues to offer A100, H100 and H200 alongside Blackwell-generation B200/B300 and GB200/GB300, while a separate primary publication records Rubin production workloads. This is direct evidence of multi-generation commercial coexistence and blocks a hard successor-arrival=immediate-commercial-exit model. It does not reveal installed fleet shares, utilisation, realised revenue by generation, residual values or positive unit economics of older hardware."
