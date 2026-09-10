module DASHI.ComputerScience.GPUBackendPrimaryAttributionSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as SnowballAttribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as ExternalIdentity

------------------------------------------------------------------------
-- CUDA / ROCm PRIMARY-SOURCE ATTRIBUTION
--
-- Primary vendor documentation is used for programming-model semantics.
-- Wikidata QIDs are supplemental external identities only.
------------------------------------------------------------------------

cudaProgrammingGuideSource : Attribution.AttributedSource
cudaProgrammingGuideSource =
  Attribution.mkNoDOISource
    "NVIDIA"
    "CUDA Programming Guide"
    "NVIDIA CUDA Toolkit Documentation"
    "2026"
    "https://docs.nvidia.com/cuda/cuda-programming-guide/"
    Attribution.technicalStandardSource
    "primary vendor source for CUDA heterogeneous host/device execution, GPU kernels, device memory, streams/synchronization, toolkit/driver separation, and compute-capability-labelled binaries"
    Attribution.publicAttribution

rocmProgrammingGuideSource : Attribution.AttributedSource
rocmProgrammingGuideSource =
  Attribution.mkNoDOISource
    "AMD"
    "AMD GPU programming on ROCm / HIP documentation"
    "AMD ROCm Documentation"
    "2026"
    "https://rocm.docs.amd.com/en/develop/reference/hip-programming.html"
    Attribution.technicalStandardSource
    "primary vendor source for ROCm heterogeneous CPU/GPU execution and HIP host/device/kernel/runtime semantics; documents CUDA-porting compatibility without claiming drop-in equivalence"
    Attribution.publicAttribution

gpuBackendSourceAtlas : Attribution.AttributedSourceAtlas
gpuBackendSourceAtlas =
  Attribution.mkSourceAtlas
    "CUDA and ROCm backend attribution"
    "DASHI.ComputerScience.GPUBackendPrimaryAttributionSnowballExact"
    (cudaProgrammingGuideSource ∷ rocmProgrammingGuideSource ∷ [])
    "retains vendor, platform, source role, canonical URL, and non-authority boundaries for GPU backend formalisation"

cudaSnowball : SnowballAttribution.SourceRoleSnowballReceipt cudaProgrammingGuideSource
cudaSnowball = SnowballAttribution.canonicalSourceRoleSnowballReceipt cudaProgrammingGuideSource

rocmSnowball : SnowballAttribution.SourceRoleSnowballReceipt rocmProgrammingGuideSource
rocmSnowball = SnowballAttribution.canonicalSourceRoleSnowballReceipt rocmProgrammingGuideSource

------------------------------------------------------------------------
-- QID / external identity coordinates.
------------------------------------------------------------------------

cudaQID : ExternalIdentity.ExternalIdentityDemand
cudaQID =
  ExternalIdentity.mkOptionalIdentityDemand
    "GPU backend identity"
    "CUDA NVIDIA parallel computing platform programming model"
    "CUDA"
    ExternalIdentity.wikidataQid
    (ExternalIdentity.verified "Wikidata" "Q477690")

rocmQID : ExternalIdentity.ExternalIdentityDemand
rocmQID =
  ExternalIdentity.mkOptionalIdentityDemand
    "GPU backend identity"
    "ROCm AMD parallel computing platform API"
    "ROCm"
    ExternalIdentity.wikidataQid
    (ExternalIdentity.verified "Wikidata" "Q110612569")

nvidiaQID : ExternalIdentity.ExternalIdentityDemand
nvidiaQID =
  ExternalIdentity.mkOptionalIdentityDemand
    "GPU vendor identity"
    "NVIDIA company"
    "NVIDIA"
    ExternalIdentity.wikidataQid
    (ExternalIdentity.verified "Wikidata" "Q182477")

amdQID : ExternalIdentity.ExternalIdentityDemand
amdQID =
  ExternalIdentity.mkOptionalIdentityDemand
    "GPU vendor identity"
    "AMD Advanced Micro Devices company"
    "AMD"
    ExternalIdentity.wikidataQid
    (ExternalIdentity.verified "Wikidata" "Q128896")

------------------------------------------------------------------------
-- Attribution firewalls.
------------------------------------------------------------------------

data QIDImpliesVendorTechnicalClaim : Set where
data VendorDocsImplyIndependentBenchmark : Set where
data HIPCompatibilityImpliesDropInEquivalence : Set where
data SameKernelVocabularyImpliesSameRuntime : Set where

qidDoesNotPayVendorClaim : QIDImpliesVendorTechnicalClaim → ⊥
qidDoesNotPayVendorClaim ()

vendorDocsDoNotCreateIndependentBenchmark : VendorDocsImplyIndependentBenchmark → ⊥
vendorDocsDoNotCreateIndependentBenchmark ()

hipCompatibilityDoesNotMeanDropInEquivalence : HIPCompatibilityImpliesDropInEquivalence → ⊥
hipCompatibilityDoesNotMeanDropInEquivalence ()

sharedVocabularyDoesNotIdentifyRuntime : SameKernelVocabularyImpliesSameRuntime → ⊥
sharedVocabularyDoesNotIdentifyRuntime ()

record GPUBackendAttributionBoundary : Set where
  constructor gpu-backend-attribution-boundary
  field
    cudaPrimaryVendorSourceRetained : Bool
    rocmPrimaryVendorSourceRetained : Bool
    cudaQIDRetained : Bool
    rocmQIDRetained : Bool
    qidCreatesTechnicalAuthority : Bool
    compatibilityCreatesImplementationIdentity : Bool
open GPUBackendAttributionBoundary public

canonicalGPUBackendAttributionBoundary : GPUBackendAttributionBoundary
canonicalGPUBackendAttributionBoundary =
  gpu-backend-attribution-boundary true true true true false false
