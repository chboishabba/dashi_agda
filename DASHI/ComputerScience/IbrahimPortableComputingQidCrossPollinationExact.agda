module DASHI.ComputerScience.IbrahimPortableComputingQidCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.IbrahimSnowballPortableComputingQidsExact as Ibrahim
import DASHI.ComputerScience.RustPortableKernelSIMDSWARBackendSnowballExact as Portable
import DASHI.ComputerScience.CUDAROCmExecutionBackendFibreExact as GPU
import DASHI.ComputerScience.TriadicCodecSWARPortableKernelCrossPollinationExact as Codec

------------------------------------------------------------------------
-- IBRAHIM / PORTABLE-COMPUTING CROSS-POLLINATION
--
-- The Wikimedia graph is an external navigation/identity fibre over the actual
-- CS formalism.  It can help discover missing axes, but it cannot supply a
-- backend lowering, implementation, ISA, execution trace, performance result,
-- codec realization, or source-provenance theorem.
------------------------------------------------------------------------

qidBoundary : Ibrahim.IbrahimPortableComputingQidBoundary
qidBoundary = Ibrahim.canonicalIbrahimPortableComputingQidBoundary

portableBoundary : Portable.RustPortableKernelBoundary
portableBoundary = Portable.canonicalRustPortableKernelBoundary

gpuBoundary : GPU.CUDAROCmBackendBoundary
gpuBoundary = GPU.canonicalCUDAROCmBackendBoundary

codecBoundary : Codec.TriadicCodecSWARPortableBoundary
codecBoundary = Codec.canonicalTriadicCodecSWARPortableBoundary

------------------------------------------------------------------------
-- A concrete Ibrahim non-factorability witness.
--
-- Two executions may both be visible as "parallel computing" to an external
-- classificatory observer while the implementation consumer still needs to
-- distinguish CPU SIMD from a GPU lockstep plane.  Therefore implementation
-- reading cannot factor through the coarse graph surface.
------------------------------------------------------------------------

data ParallelClassifiedCase : Set where
  cpuSIMDCase : ParallelClassifiedCase
  gpuPlaneCase : ParallelClassifiedCase

data ParallelGraphSurface : Set where
  parallelComputingSurface : ParallelGraphSurface

data ImplementationReading : Set where
  cpuSIMDImplementation : ImplementationReading
  gpuPlaneImplementation : ImplementationReading

projectParallelGraph : ParallelClassifiedCase → ParallelGraphSurface
projectParallelGraph _ = parallelComputingSurface

implementationReading : ParallelClassifiedCase → ImplementationReading
implementationReading cpuSIMDCase = cpuSIMDImplementation
implementationReading gpuPlaneCase = gpuPlaneImplementation

parallelGraphImplementationDefect :
  INF.NonFactorabilityWitness projectParallelGraph implementationReading
parallelGraphImplementationDefect = INF.nonFactorabilityWitness
  cpuSIMDCase gpuPlaneCase refl (λ ())

parallelGraphCannotFactorImplementation :
  INF.FactorsThrough projectParallelGraph implementationReading → ⊥
parallelGraphCannotFactorImplementation =
  INF.witnessRulesOutEveryFlatFactorisation parallelGraphImplementationDefect

------------------------------------------------------------------------
-- A second witness at the representation/execution seam.
--
-- The same codec packed-word candidate can be presented to multiple backend
-- lowerings.  Merely knowing that the workload is associated with SIMD/SWAR-
-- adjacent concepts cannot recover whether a concrete target was CPU-vector,
-- packed scalar, CUDA, or ROCm.
------------------------------------------------------------------------

data SameCodecCandidateCase : Set where
  codecCPUVectorCase : SameCodecCandidateCase
  codecCUDACase : SameCodecCandidateCase

data CodecRepresentationSurface : Set where
  sameTriadicPackedCandidate : CodecRepresentationSurface

data CodecBackendReading : Set where
  codecCPUVectorBackend : CodecBackendReading
  codecCUDABackend : CodecBackendReading

projectCodecRepresentation : SameCodecCandidateCase → CodecRepresentationSurface
projectCodecRepresentation _ = sameTriadicPackedCandidate

codecBackendReading : SameCodecCandidateCase → CodecBackendReading
codecBackendReading codecCPUVectorCase = codecCPUVectorBackend
codecBackendReading codecCUDACase = codecCUDABackend

codecRepresentationBackendDefect :
  INF.NonFactorabilityWitness projectCodecRepresentation codecBackendReading
codecRepresentationBackendDefect = INF.nonFactorabilityWitness
  codecCPUVectorCase codecCUDACase refl (λ ())

codecRepresentationCannotFactorBackend :
  INF.FactorsThrough projectCodecRepresentation codecBackendReading → ⊥
codecRepresentationCannotFactorBackend =
  INF.witnessRulesOutEveryFlatFactorisation codecRepresentationBackendDefect

------------------------------------------------------------------------
-- Selected graph-to-formalism correspondences.
--
-- These state only that the external identity is relevant to a formal axis.
-- They do not claim Wikidata pays the corresponding implementation semantics.
------------------------------------------------------------------------

record QidFormalAxisReceipt : Set where
  constructor qid-formal-axis-receipt
  field
    externalIdentityRetained : Bool
    correspondingFormalAxisPresent : Bool
    qidPaysFormalSemantics : Bool
    qidPaysExecutionReceipt : Bool
    qidPaysPerformanceReceipt : Bool
open QidFormalAxisReceipt public

simdAxisReceipt : QidFormalAxisReceipt
simdAxisReceipt = qid-formal-axis-receipt true true false false false

gpuAxisReceipt : QidFormalAxisReceipt
gpuAxisReceipt = qid-formal-axis-receipt true true false false false

cudaAxisReceipt : QidFormalAxisReceipt
cudaAxisReceipt = qid-formal-axis-receipt true true false false false

rocmAxisReceipt : QidFormalAxisReceipt
rocmAxisReceipt = qid-formal-axis-receipt true true false false false

armAxisReceipt : QidFormalAxisReceipt
armAxisReceipt = qid-formal-axis-receipt true true false false false

tensorAcceleratorAxisReceipt : QidFormalAxisReceipt
tensorAcceleratorAxisReceipt = qid-formal-axis-receipt true true false false false

swarUnresolvedAxisReceipt : QidFormalAxisReceipt
swarUnresolvedAxisReceipt = qid-formal-axis-receipt false true false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data QidClassificationDeterminesBackend : Set where
data SIMDClassificationDeterminesLaneWidth : Set where
data ARMClassificationDeterminesInstructionSetRevision : Set where
data GPUClassificationDeterminesWarpWavefrontWidth : Set where
data GPGPUClassificationDeterminesCUDA : Set where
data AcceleratorClassificationDeterminesTensorInstruction : Set where
data SWARQidAbsenceBlocksSWARFormalisation : Set where
data ExternalGraphDeterminesCodecPerformance : Set where

qidClassificationDoesNotDetermineBackend : QidClassificationDeterminesBackend → ⊥
qidClassificationDoesNotDetermineBackend ()

simdClassificationDoesNotDetermineLaneWidth : SIMDClassificationDeterminesLaneWidth → ⊥
simdClassificationDoesNotDetermineLaneWidth ()

armClassificationDoesNotBindISARevision : ARMClassificationDeterminesInstructionSetRevision → ⊥
armClassificationDoesNotBindISARevision ()

gpuClassificationDoesNotDeterminePlaneWidth : GPUClassificationDeterminesWarpWavefrontWidth → ⊥
gpuClassificationDoesNotDeterminePlaneWidth ()

gpgpuClassificationDoesNotSelectCUDA : GPGPUClassificationDeterminesCUDA → ⊥
gpgpuClassificationDoesNotSelectCUDA ()

acceleratorClassificationDoesNotSelectTensorInstruction :
  AcceleratorClassificationDeterminesTensorInstruction → ⊥
acceleratorClassificationDoesNotSelectTensorInstruction ()

missingSWARQidDoesNotBlockFormalisation : SWARQidAbsenceBlocksSWARFormalisation → ⊥
missingSWARQidDoesNotBlockFormalisation ()

graphDoesNotDetermineCodecPerformance : ExternalGraphDeterminesCodecPerformance → ⊥
graphDoesNotDetermineCodecPerformance ()

record IbrahimPortableComputingCrossPollinationBoundary : Set where
  constructor ibrahim-portable-computing-cross-pollination-boundary
  field
    existingIbrahimQidLayerReused : Bool
    externalGraphCanDiscoverRelevantAxes : Bool
    externalGraphExhaustsImplementationState : Bool
    parallelClassificationFactorsImplementation : Bool
    packedCodecRepresentationFactorsBackendChoice : Bool
    unresolvedSWARIdentityRetained : Bool
    vendorPrimarySourcesStillOwnBackendSemantics : Bool
    exactRuntimePerformancePaidByQidGraph : Bool
open IbrahimPortableComputingCrossPollinationBoundary public

canonicalIbrahimPortableComputingCrossPollinationBoundary :
  IbrahimPortableComputingCrossPollinationBoundary
canonicalIbrahimPortableComputingCrossPollinationBoundary =
  ibrahim-portable-computing-cross-pollination-boundary
    true true false false false true true false
