module DASHI.ComputerScience.IbrahimPortableComputingSecondHopCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.IbrahimSnowballPortableComputingSecondHopExact as Ibrahim
import DASHI.ComputerScience.RustPortableKernelSIMDSWARBackendSnowballExact as Portable
import DASHI.ComputerScience.CUDAROCmExecutionBackendFibreExact as GPU
import DASHI.ComputerScience.TriadicCodecSWARPortableKernelCrossPollinationExact as Codec

------------------------------------------------------------------------
-- SECOND-HOP COMPUTING CROSS-POLLINATION
--
-- External classification is deliberately coarser than implementation.  The
-- same portable logical operation can inhabit Flynn/SIMD/heterogeneous or
-- accelerator-facing taxonomies while retaining backend, vector-width,
-- offload, and matrix-unit residuals.
------------------------------------------------------------------------

ibrahimBoundary : Ibrahim.PortableComputingSecondHopBoundary
ibrahimBoundary = Ibrahim.canonicalPortableComputingSecondHopBoundary

portableBoundary : Portable.SIMDSWARBoundary
portableBoundary = Portable.canonicalSIMDSWARBoundary

codecBoundary : Codec.TriadicCodecSWARPortableBoundary
codecBoundary = Codec.canonicalTriadicCodecSWARPortableBoundary

------------------------------------------------------------------------
-- Witness 1: same coarse SIMD category, different Arm vector contracts.
------------------------------------------------------------------------

data ArmVectorCase : Set where
  neonFixedWidthCase : ArmVectorCase
  sveScalableCase : ArmVectorCase

data SIMDSurface : Set where
  sameSIMDClassification : SIMDSurface

data ArmVectorReading : Set where
  fixedWidthAdvancedSIMD : ArmVectorReading
  scalableVectorLengthAgnostic : ArmVectorReading

projectSIMD : ArmVectorCase → SIMDSurface
projectSIMD _ = sameSIMDClassification

readArmVector : ArmVectorCase → ArmVectorReading
readArmVector neonFixedWidthCase = fixedWidthAdvancedSIMD
readArmVector sveScalableCase = scalableVectorLengthAgnostic

simdArmVectorDefect : INF.NonFactorabilityWitness projectSIMD readArmVector
simdArmVectorDefect = INF.nonFactorabilityWitness
  neonFixedWidthCase sveScalableCase refl (λ ())

simdCannotRecoverArmVectorContract :
  INF.FactorsThrough projectSIMD readArmVector → ⊥
simdCannotRecoverArmVectorContract =
  INF.witnessRulesOutEveryFlatFactorisation simdArmVectorDefect

------------------------------------------------------------------------
-- Witness 2: same host-offload surface, different target execution backend.
------------------------------------------------------------------------

data OffloadCase : Set where
  offloadToCUDA : OffloadCase
  offloadToROCm : OffloadCase

data OffloadSurface : Set where
  sameHostTargetOffload : OffloadSurface

data OffloadBackendReading : Set where
  cudaBackendReading : OffloadBackendReading
  rocmBackendReading : OffloadBackendReading

projectOffload : OffloadCase → OffloadSurface
projectOffload _ = sameHostTargetOffload

readOffloadBackend : OffloadCase → OffloadBackendReading
readOffloadBackend offloadToCUDA = cudaBackendReading
readOffloadBackend offloadToROCm = rocmBackendReading

offloadBackendDefect : INF.NonFactorabilityWitness projectOffload readOffloadBackend
offloadBackendDefect = INF.nonFactorabilityWitness
  offloadToCUDA offloadToROCm refl (λ ())

offloadSurfaceCannotRecoverBackend :
  INF.FactorsThrough projectOffload readOffloadBackend → ⊥
offloadSurfaceCannotRecoverBackend =
  INF.witnessRulesOutEveryFlatFactorisation offloadBackendDefect

------------------------------------------------------------------------
-- Witness 3: same matrix-multiplication consumer, different realization.
------------------------------------------------------------------------

data MatrixExecutionCase : Set where
  cpuVectorMatrixCase : MatrixExecutionCase
  tpuSystolicMatrixCase : MatrixExecutionCase

data MatrixConsumerSurface : Set where
  sameMatrixMultiplication : MatrixConsumerSurface

data MatrixRealizationReading : Set where
  vectorInstructionRealization : MatrixRealizationReading
  systolicMXURealization : MatrixRealizationReading

projectMatrixConsumer : MatrixExecutionCase → MatrixConsumerSurface
projectMatrixConsumer _ = sameMatrixMultiplication

readMatrixRealization : MatrixExecutionCase → MatrixRealizationReading
readMatrixRealization cpuVectorMatrixCase = vectorInstructionRealization
readMatrixRealization tpuSystolicMatrixCase = systolicMXURealization

matrixRealizationDefect :
  INF.NonFactorabilityWitness projectMatrixConsumer readMatrixRealization
matrixRealizationDefect = INF.nonFactorabilityWitness
  cpuVectorMatrixCase tpuSystolicMatrixCase refl (λ ())

matrixConsumerCannotRecoverRealization :
  INF.FactorsThrough projectMatrixConsumer readMatrixRealization → ⊥
matrixConsumerCannotRecoverRealization =
  INF.witnessRulesOutEveryFlatFactorisation matrixRealizationDefect

------------------------------------------------------------------------
-- Portable-kernel consequence.
------------------------------------------------------------------------

record PortableOperationResidual : Set where
  constructor portable-operation-residual
  field
    sameSourceLevelOperation : Bool
    targetBackendKnown : Bool
    vectorContractKnown : Bool
    offloadModelKnown : Bool
    matrixAcceleratorKnown : Bool
    exactISARevisionKnown : Bool
    exactLaneOrVectorWidthKnown : Bool
    measuredLatencyKnown : Bool
    measuredEnergyKnown : Bool
open PortableOperationResidual public

cpuSIMDResidual : PortableOperationResidual
cpuSIMDResidual = portable-operation-residual true true true false false false false false false

gpuOffloadResidual : PortableOperationResidual
gpuOffloadResidual = portable-operation-residual true true false true false false false false false

tpuMatrixResidual : PortableOperationResidual
tpuMatrixResidual = portable-operation-residual true true false true true false false false false

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data SameSIMDClassImpliesSameVectorWidth : Set where
data SameOffloadModelImpliesSameBackend : Set where
data SameMatrixOpImpliesSameAccelerator : Set where
data SVEImpliesFasterThanNeon : Set where
data TPUImpliesGPU : Set where
data SystolicArrayImpliesSWAR : Set where
data MatrixAcceleratorImpliesCodecAcceleration : Set where

sameSIMDClassDoesNotFixWidth : SameSIMDClassImpliesSameVectorWidth → ⊥
sameSIMDClassDoesNotFixWidth ()

sameOffloadDoesNotFixBackend : SameOffloadModelImpliesSameBackend → ⊥
sameOffloadDoesNotFixBackend ()

sameMatrixOpDoesNotFixAccelerator : SameMatrixOpImpliesSameAccelerator → ⊥
sameMatrixOpDoesNotFixAccelerator ()

sveDoesNotCreatePerformanceOrdering : SVEImpliesFasterThanNeon → ⊥
sveDoesNotCreatePerformanceOrdering ()

tpuDoesNotBecomeGPU : TPUImpliesGPU → ⊥
tpuDoesNotBecomeGPU ()

systolicDoesNotBecomeSWAR : SystolicArrayImpliesSWAR → ⊥
systolicDoesNotBecomeSWAR ()

acceleratorDoesNotCreateCodecSpeedup : MatrixAcceleratorImpliesCodecAcceleration → ⊥
acceleratorDoesNotCreateCodecSpeedup ()

record PortableComputingSecondHopCrossPollinationBoundary : Set where
  constructor portable-computing-second-hop-cross-pollination-boundary
  field
    simdToArmVectorResidualProved : Bool
    offloadToBackendResidualProved : Bool
    matrixOperationToRealizationResidualProved : Bool
    portableKernelSubstrateReused : Bool
    codecSubstrateReused : Bool
    taxonomyCreatesRuntimeIdentity : Bool
    matrixConsumerCreatesAcceleratorIdentity : Bool
    currentAxisVocabularyClaimedComplete : Bool
open PortableComputingSecondHopCrossPollinationBoundary public

canonicalPortableComputingSecondHopCrossPollinationBoundary :
  PortableComputingSecondHopCrossPollinationBoundary
canonicalPortableComputingSecondHopCrossPollinationBoundary =
  portable-computing-second-hop-cross-pollination-boundary
    true true true true true false false false
