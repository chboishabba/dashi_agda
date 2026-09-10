module DASHI.ComputerScience.CUDAROCmExecutionBackendFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.GPUBackendPrimaryAttributionSnowballExact as Source
import DASHI.ComputerScience.HelloWorldBinaryTernaryExecutionCostComparisonExact as HelloCost
import DASHI.ComputerScience.HelloWorldBinaryTernaryExecutionPathBidiExact as HelloBidi
import DASHI.ComputerScience.RSA260CADOInterfaceCompatibilitySnowballExact as RSA260Interface

------------------------------------------------------------------------
-- GPU BACKEND AS A PEER REALISATION FIBRE
--
-- A logical execution/representation can be lowered to a backend, but the
-- backend does not redefine the logical semantics.  Conversely, logical cell
-- count or shared output does not determine GPU latency, energy, silicon area,
-- kernel count, or implementation identity.
------------------------------------------------------------------------

data GPUBackendKind : Set where
  cudaBackend : GPUBackendKind
  rocmHIPBackend : GPUBackendKind
  unresolvedGPUBackend : GPUBackendKind

data BackendRelation : Set where
  logicalExecutionLoweredToBackend : BackendRelation
  hostLaunchesDeviceKernel : BackendRelation
  hostDeviceMemoryTransfer : BackendRelation
  backendStreamOrQueueOrdersWork : BackendRelation
  backendSynchronizesWork : BackendRelation
  backendImplementsUpstreamInterfaceSlot : BackendRelation

record GPUBackendExecutionReceipt : Set where
  constructor gpu-backend-execution-receipt
  field
    backend : GPUBackendKind
    relation : BackendRelation
    logicalProgramReference : String
    backendProgramReference : String
    hostReference : String
    deviceReference : String
    sourceReference : String
    sourceRole : String
    exactBackendSourceRevisionBound : Bool
    exactDeviceModelBound : Bool
    measuredLatencyBound : Bool
    measuredEnergyBound : Bool
    sameLogicalSemanticsPaid : Bool
open GPUBackendExecutionReceipt public

cudaProgrammingModelReceipt : GPUBackendExecutionReceipt
cudaProgrammingModelReceipt =
  gpu-backend-execution-receipt
    cudaBackend
    hostLaunchesDeviceKernel
    "consumer logical program"
    "CUDA GPU kernel"
    "CPU host / host memory"
    "NVIDIA GPU / device memory"
    "NVIDIA CUDA Programming Guide"
    "primary vendor programming-model semantics"
    false false false false false

rocmProgrammingModelReceipt : GPUBackendExecutionReceipt
rocmProgrammingModelReceipt =
  gpu-backend-execution-receipt
    rocmHIPBackend
    hostLaunchesDeviceKernel
    "consumer logical program"
    "HIP kernel"
    "CPU host"
    "AMD GPU device"
    "AMD ROCm / HIP documentation"
    "primary vendor programming-model semantics"
    false false false false false

------------------------------------------------------------------------
-- Hello World cross-pollination.
--
-- The existing Hello World theorem proves the decoded binary/ternary paths are
-- the same abstract machine path.  A GPU backend is a new coordinate below
-- that theorem; it is not inferred from the logical representation.
------------------------------------------------------------------------

helloWorldSharedExecutionReceipt :
  HelloCost.SharedExecutionDifferentRepresentationReceipt
helloWorldSharedExecutionReceipt =
  HelloCost.canonicalSharedExecutionDifferentRepresentationReceipt

helloWorldExecutionBoundary : HelloCost.ExecutionCostComparisonBoundary
helloWorldExecutionBoundary = HelloCost.canonicalExecutionCostComparisonBoundary

helloWorldBidiBoundary : HelloBidi.HelloWorldBinaryTernaryExecutionBidiBoundary
helloWorldBidiBoundary = HelloBidi.canonicalHelloWorldBinaryTernaryExecutionBidiBoundary

record HelloWorldGPUBackendCrossPollination : Set where
  constructor hello-world-gpu-backend-cross-pollination
  field
    binaryAndTernaryLogicalPathSame : Bool
    backendSelectionIsIndependentAxis : Bool
    binaryLogicalRepresentationForcesCUDA : Bool
    ternaryLogicalRepresentationForcesROCm : Bool
    fewerLogicalCellsProvesLowerGPUEnergy : Bool
    sameLogicalOutputProvesSameKernelTrace : Bool
open HelloWorldGPUBackendCrossPollination public

canonicalHelloWorldGPUBackendCrossPollination : HelloWorldGPUBackendCrossPollination
canonicalHelloWorldGPUBackendCrossPollination =
  hello-world-gpu-backend-cross-pollination true true false false false false

------------------------------------------------------------------------
-- RSA-260 interface cross-pollination.
------------------------------------------------------------------------

rsa260CUDAInterfaceDelta : RSA260Interface.InterfaceCompatibilityReceipt
rsa260CUDAInterfaceDelta = RSA260Interface.bwcMMImplCompatibility

record RSA260GPUBackendCrossPollination : Set where
  constructor rsa260-gpu-backend-cross-pollination
  field
    upstreamMMImplSlotRetained : Bool
    cudaValueTypedAsDownstreamExtension : Bool
    cudaPlatformDocsIdentifyLuDevinSource : Bool
    stockCUDAImpliesRSA260CUDAImplementation : Bool
open RSA260GPUBackendCrossPollination public

canonicalRSA260GPUBackendCrossPollination : RSA260GPUBackendCrossPollination
canonicalRSA260GPUBackendCrossPollination =
  rsa260-gpu-backend-cross-pollination true true false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data LogicalRadixDeterminesGPUBackend : Set where
data SameOutputDeterminesBackendTrace : Set where
data GPUBackendDeterminesQuantumExecution : Set where
data CUDAAndHIPCompatibilityMeansSameBinary : Set where
data BackendNameDeterminesPhysicalCost : Set where

radixDoesNotDetermineBackend : LogicalRadixDeterminesGPUBackend → ⊥
radixDoesNotDetermineBackend ()

sameOutputDoesNotDetermineTrace : SameOutputDeterminesBackendTrace → ⊥
sameOutputDoesNotDetermineTrace ()

gpuBackendDoesNotCreateQuantumExecution : GPUBackendDeterminesQuantumExecution → ⊥
gpuBackendDoesNotCreateQuantumExecution ()

portabilityDoesNotCreateBinaryIdentity : CUDAAndHIPCompatibilityMeansSameBinary → ⊥
portabilityDoesNotCreateBinaryIdentity ()

backendNameDoesNotDeterminePhysicalCost : BackendNameDeterminesPhysicalCost → ⊥
backendNameDoesNotDeterminePhysicalCost ()

record CUDAROCmBackendBoundary : Set where
  constructor cuda-rocm-backend-boundary
  field
    cudaAndROCmArePeerBackendFibres : Bool
    hostDeviceSeparationRetained : Bool
    logicalExecutionSeparateFromBackendExecution : Bool
    representationSeparateFromPhysicalBackend : Bool
    quantumExecutionSeparateFromGPUKernelExecution : Bool
    exactPerformanceComparisonPaid : Bool
open CUDAROCmBackendBoundary public

canonicalCUDAROCmBackendBoundary : CUDAROCmBackendBoundary
canonicalCUDAROCmBackendBoundary =
  cuda-rocm-backend-boundary true true true true true false
