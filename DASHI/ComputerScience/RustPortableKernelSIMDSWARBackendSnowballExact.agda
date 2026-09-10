module DASHI.ComputerScience.RustPortableKernelSIMDSWARBackendSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as SnowballAttribution
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as ExternalIdentity
import DASHI.ComputerScience.CUDAROCmExecutionBackendFibreExact as GPU
import DASHI.ComputerScience.HelloWorldBinaryTernaryExecutionPathBidiExact as Hello

------------------------------------------------------------------------
-- RUST PORTABLE-KERNEL / SIMD-SWAR BACKEND SNOWBALL
--
-- CubeCL is used as a concrete Rust witness that one source-level kernel
-- abstraction may lower to several heterogeneous backends. Burn is retained as
-- a higher tensor/backend consumer. Neither source is treated as proving equal
-- performance, one binary, one schedule, or support for every accelerator.
--
-- SIMD/SWAR live BELOW the source-level program as possible physical/lowering
-- realizations. A CPU SIMD vector, packed scalar/SWAR-like operation, GPU
-- subgroup/warp/wavefront, and tensor-matrix accelerator may agree under a
-- higher logical consumer while remaining different execution objects.
------------------------------------------------------------------------

cubeCLSource : Attribution.AttributedSource
cubeCLSource =
  Attribution.mkNoDOISource
    "Tracel AI / CubeCL contributors"
    "CubeCL"
    "CubeCL project documentation and source repository"
    "2026"
    "https://github.com/tracel-ai/cubecl"
    Attribution.practitionerSource
    "primary project source for a Rust multi-platform compute-language abstraction targeting CUDA, ROCm/HIP, Metal, Vulkan/SPIR-V, WebGPU/WGSL, and CPU; CPU execution may use SIMD where available"
    Attribution.publicAttribution

burnSource : Attribution.AttributedSource
burnSource =
  Attribution.mkNoDOISource
    "Tracel AI / Burn contributors"
    "Burn"
    "Burn project documentation and source repository"
    "2026"
    "https://github.com/tracel-ai/burn"
    Attribution.practitionerSource
    "primary project source for backend-generic Rust tensor programs with swappable CUDA, ROCm, Vulkan/WebGPU, CPU and related backend implementations"
    Attribution.publicAttribution

portableKernelSourceAtlas : Attribution.AttributedSourceAtlas
portableKernelSourceAtlas =
  Attribution.mkSourceAtlas
    "Rust portable heterogeneous kernel attribution"
    "DASHI.ComputerScience.RustPortableKernelSIMDSWARBackendSnowballExact"
    (cubeCLSource ∷ burnSource ∷ [])
    "retains project authorship, source role, canonical URL, backend support claims, and non-equivalence boundaries"

cubeCLSnowball : SnowballAttribution.SourceRoleSnowballReceipt cubeCLSource
cubeCLSnowball = SnowballAttribution.canonicalSourceRoleSnowballReceipt cubeCLSource

burnSnowball : SnowballAttribution.SourceRoleSnowballReceipt burnSource
burnSnowball = SnowballAttribution.canonicalSourceRoleSnowballReceipt burnSource

------------------------------------------------------------------------
-- External identities.
------------------------------------------------------------------------

rustQID : ExternalIdentity.ExternalIdentityDemand
rustQID =
  ExternalIdentity.mkOptionalIdentityDemand
    "portable-kernel language identity"
    "Rust programming language"
    "Rust"
    ExternalIdentity.wikidataQid
    (ExternalIdentity.verified "Wikidata" "Q575650")

cubeCLQID : ExternalIdentity.ExternalIdentityDemand
cubeCLQID =
  ExternalIdentity.mkOptionalIdentityDemand
    "portable-kernel project identity"
    "CubeCL Rust compute language Tracel AI"
    "CubeCL"
    ExternalIdentity.wikidataQid
    (ExternalIdentity.unresolved "no exact CubeCL Wikidata item verified in this acquisition pass")

burnQID : ExternalIdentity.ExternalIdentityDemand
burnQID =
  ExternalIdentity.mkOptionalIdentityDemand
    "tensor framework project identity"
    "Burn Rust deep learning framework Tracel AI"
    "Burn"
    ExternalIdentity.wikidataQid
    (ExternalIdentity.unresolved "no exact Burn framework Wikidata item verified in this acquisition pass")

------------------------------------------------------------------------
-- Portable source and lowering carriers.
------------------------------------------------------------------------

data PortableTarget : Set where
  cudaTarget rocmHIPTarget vulkanTarget webGPUTarget metalTarget
  cpuX86Target cpuARMTarget unresolvedTarget : PortableTarget

data ParallelLoweringKind : Set where
  scalarLowering : ParallelLoweringKind
  simdVectorLowering : ParallelLoweringKind
  packedScalarLowering : ParallelLoweringKind
  lockstepPlaneLowering : ParallelLoweringKind
  workgroupLowering : ParallelLoweringKind
  tensorMatrixAcceleratorLowering : ParallelLoweringKind

data PortableRelation : Set where
  oneSourceKernelToMultipleTargets : PortableRelation
  tensorProgramGenericOverBackend : PortableRelation
  vectorAxisToSIMDOrPackedScalar : PortableRelation
  planeAxisToWarpWavefrontSubgroup : PortableRelation
  targetFeatureSelectsSpecialization : PortableRelation

record PortableLoweringReceipt : Set where
  constructor portable-lowering-receipt
  field
    sourceProgramReference : String
    target : PortableTarget
    lowering : ParallelLoweringKind
    relation : PortableRelation
    sourceReference : String
    sameSourceLevelProgram : Bool
    sameCompiledBinary : Bool
    samePhysicalSchedule : Bool
    samePerformance : Bool
    exactTargetISA : Bool
open PortableLoweringReceipt public

cubeCLCUDA : PortableLoweringReceipt
cubeCLCUDA = portable-lowering-receipt
  "CubeCL Rust kernel" cudaTarget lockstepPlaneLowering
  oneSourceKernelToMultipleTargets
  "CubeCL primary project documentation: CUDA runtime/compiler target"
  true false false false false

cubeCLROCm : PortableLoweringReceipt
cubeCLROCm = portable-lowering-receipt
  "CubeCL Rust kernel" rocmHIPTarget lockstepPlaneLowering
  oneSourceKernelToMultipleTargets
  "CubeCL primary project documentation: ROCm/HIP runtime/compiler target"
  true false false false false

cubeCLCPUARM : PortableLoweringReceipt
cubeCLCPUARM = portable-lowering-receipt
  "CubeCL Rust kernel" cpuARMTarget simdVectorLowering
  oneSourceKernelToMultipleTargets
  "CubeCL documents a Rust CPU backend with SIMD where available; Burn documents ARM CPU backend support"
  true false false false false

------------------------------------------------------------------------
-- SIMD / SWAR relationship.
--
-- CubeCL's environment abstraction currently describes a Vector axis mapping
-- to SIMD lanes and packed scalar operations. The latter is deliberately kept
-- as `packedScalarLowering`, not promoted to historical/technical SWAR identity
-- without a source explicitly making that equivalence.
------------------------------------------------------------------------

record SIMDSWARBoundary : Set where
  constructor simd-swar-boundary
  field
    simdAlreadyAppearsInRepoAsOperationalCostAxis : Bool
    dedicatedSWAROwnerPreviouslyLocated : Bool
    cubeVectorAxisCanMapToSIMDLanes : Bool
    cubeVectorAxisCanMapToPackedScalarOps : Bool
    packedScalarAutomaticallyEqualsNamedSWARTechnique : Bool
    cpuSIMDIsGPUWarpOrWavefront : Bool
    tensorMatrixAccelerationIsOrdinarySIMD : Bool
open SIMDSWARBoundary public

canonicalSIMDSWARBoundary : SIMDSWARBoundary
canonicalSIMDSWARBoundary =
  simd-swar-boundary true false true true false false false

------------------------------------------------------------------------
-- Existing CUDA/ROCm + Hello World cross-pollination.
------------------------------------------------------------------------

existingGPUBackendBoundary : GPU.CUDAROCmBackendBoundary
existingGPUBackendBoundary = GPU.canonicalCUDAROCmBackendBoundary

helloWorldBidiBoundary : Hello.HelloWorldBinaryTernaryExecutionBidiBoundary
helloWorldBidiBoundary = Hello.canonicalHelloWorldBinaryTernaryExecutionBidiBoundary

record PortableHelloWorldBoundary : Set where
  constructor portable-hello-world-boundary
  field
    sameLogicalProgramMayLowerToSeveralBackends : Bool
    binaryTernaryEncodingDeterminesPortableTarget : Bool
    sameSourceMeansSameBinary : Bool
    sameSemanticsMeansSamePhysicalSchedule : Bool
    backendSupportMeansEqualPerformance : Bool
open PortableHelloWorldBoundary public

canonicalPortableHelloWorldBoundary : PortableHelloWorldBoundary
canonicalPortableHelloWorldBoundary =
  portable-hello-world-boundary true false false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SingleSourceImpliesSingleBinary : Set where
data BackendSupportImpliesPerformancePortability : Set where
data CPUARMTargetImpliesARMISAReceipt : Set where
data TensorBackendImpliesTensorCoreUse : Set where
data SIMDImpliesSWARIdentity : Set where
data GPUPlaneImpliesCPUSIMDIdentity : Set where

aSingleSourceDoesNotMeanSingleBinary : SingleSourceImpliesSingleBinary → ⊥
aSingleSourceDoesNotMeanSingleBinary ()

supportDoesNotProvePerformancePortability : BackendSupportImpliesPerformancePortability → ⊥
supportDoesNotProvePerformancePortability ()

armBackendLabelDoesNotBindExactISA : CPUARMTargetImpliesARMISAReceipt → ⊥
armBackendLabelDoesNotBindExactISA ()

tensorBackendDoesNotRequireTensorCores : TensorBackendImpliesTensorCoreUse → ⊥
tensorBackendDoesNotRequireTensorCores ()

simdDoesNotSilentlyBecomeSWAR : SIMDImpliesSWARIdentity → ⊥
simdDoesNotSilentlyBecomeSWAR ()

gpuPlaneDoesNotBecomeCPUSIMD : GPUPlaneImpliesCPUSIMDIdentity → ⊥
gpuPlaneDoesNotBecomeCPUSIMD ()

------------------------------------------------------------------------
-- Current snowball frontier.
------------------------------------------------------------------------

record RustPortableKernelBoundary : Set where
  constructor rust-portable-kernel-boundary
  field
    rustQIDRetained : Bool
    cubeCLPrimaryProjectRetained : Bool
    burnPrimaryProjectRetained : Bool
    cudaROCmCPUARMTargetsRepresentable : Bool
    SIMDAndPackedScalarAxesRetained : Bool
    exactSWARIdentityPaid : Bool
    equalPerformanceAcrossTargetsPaid : Bool
    tensorAcceleratorUsePaidByBackendNameAlone : Bool
open RustPortableKernelBoundary public

canonicalRustPortableKernelBoundary : RustPortableKernelBoundary
canonicalRustPortableKernelBoundary =
  rust-portable-kernel-boundary true true true true true false false false
